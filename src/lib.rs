use std::collections::HashMap;
use std::fmt;
use std::fs;
use std::io;
use std::path::Path;

use nom::{
    branch::alt,
    bytes::complete::{tag, take_until},
    character::complete::{alphanumeric1, multispace0},
    combinator::{map, opt},
    multi::many0,
    sequence::separated_pair,
    sequence::{delimited, preceded, terminated},
    IResult,
};

use nom::bytes::complete::take_while1;

#[derive(Debug, Clone)]
pub enum Node {
    Text(String),
    Variable(String),
    If(String, Vec<Node>, Option<Vec<Node>>),
    For(String, String, Vec<Node>),
}

#[derive(Debug, Clone)]
pub struct Template {
    pub nodes: Vec<Node>,
}

impl Template {
    pub fn new(template: &str) -> Result<Self, String> {
        match parse_template(template) {
            Ok((_, nodes)) => Ok(Template { nodes }),
            Err(e) => match &e {
                nom::Err::Error(e) | nom::Err::Failure(e) => {
                    Err(format!("Failed to parse template: {:?}", e))
                }
                nom::Err::Incomplete(_) => Err(format!("Incomplete input")),
            },
        }
    }

    pub fn render(&self, context: &HashMap<String, Value>) -> Result<String, String> {
        render_nodes(&self.nodes, context)
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    String(String),
    Number(f64),
    Boolean(bool),
    List(Vec<Value>),
    Object(HashMap<String, Value>),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::String(s) => write!(f, "{}", s),
            Value::Number(n) => write!(f, "{}", n),
            Value::Boolean(b) => write!(f, "{}", b),
            Value::List(l) => write!(f, "{:?}", l),
            Value::Object(o) => write!(f, "{:?}", o),
        }
    }
}

fn parse_template(input: &str) -> IResult<&str, Vec<Node>> {
    many0(alt((parse_variable, parse_if, parse_for, parse_text)))(input)
}

fn parse_text(input: &str) -> IResult<&str, Node> {
    map(take_while1(|c| c != '{'), |s: &str| {
        Node::Text(s.to_string())
    })(input)
}

fn parse_variable(input: &str) -> IResult<&str, Node> {
    map(
        delimited(
            tag("{{"),
            preceded(multispace0, terminated(take_until("}}"), multispace0)),
            tag("}}"),
        ),
        |s: &str| Node::Variable(s.trim().to_string()),
    )(input)
}

fn parse_if(input: &str) -> IResult<&str, Node> {
    let (input, _) = tag("{% if ")(input)?;
    let (input, condition) = take_until(" %}")(input)?;
    let (input, _) = tag(" %}")(input)?;
    let (input, true_branch) = take_until("{% else %}")(input)?;
    let (input, else_branch) = opt(preceded(tag("{% else %}"), take_until("{% endif %}")))(input)?;
    let (input, _) = tag("{% endif %}")(input)?;

    let true_nodes = parse_template(true_branch)?.1;
    let else_nodes = else_branch.map(|eb| parse_template(eb).unwrap().1);

    Ok((
        input,
        Node::If(condition.trim().to_string(), true_nodes, else_nodes),
    ))
}

fn parse_for(input: &str) -> IResult<&str, Node> {
    let (input, _) = tag("{% for ")(input)?;
    let (input, (item, collection)) =
        separated_pair(alphanumeric1, tag(" in "), take_until(" %}"))(input)?;
    let (input, _) = tag(" %}")(input)?;
    let (input, body) = take_until("{% endfor %}")(input)?;
    let (input, _) = tag("{% endfor %}")(input)?;

    let body_nodes = parse_template(body)?.1;

    Ok((
        input,
        Node::For(item.to_string(), collection.trim().to_string(), body_nodes),
    ))
}

fn render_node(node: &Node, context: &HashMap<String, Value>) -> Result<String, String> {
    match node {
        Node::Text(text) => Ok(text.clone()),
        Node::Variable(name) => {
            let parts: Vec<&str> = name.split('.').collect();
            let mut current_value = context.get(parts[0]);

            for &part in &parts[1..] {
                match current_value {
                    Some(Value::Object(obj)) => current_value = obj.get(part),
                    _ => return Err(format!("Cannot access '{}' in '{}'", part, name)),
                }
            }

            match current_value {
                Some(value) => Ok(value.to_string()),
                None => Err(format!("Variable '{}' not found in context", name)),
            }
        }
        Node::If(condition, true_branch, else_branch) => {
            let condition_result = eval_condition(condition, context)?;
            if condition_result {
                render_nodes(true_branch, context)
            } else if let Some(else_nodes) = else_branch {
                render_nodes(else_nodes, context)
            } else {
                Ok(String::new())
            }
        }
        Node::For(item, collection, body) => {
            let items = match context.get(collection) {
                Some(Value::List(list)) => list,
                _ => {
                    return Err(format!(
                        "Collection '{}' not found or not a list",
                        collection
                    ))
                }
            };
            let mut output = String::new();
            for value in items {
                let mut loop_context = context.clone();
                loop_context.insert(item.clone(), value.clone());
                output.push_str(&render_nodes(body, &loop_context)?);
            }
            Ok(output)
        }
    }
}

fn render_nodes(nodes: &[Node], context: &HashMap<String, Value>) -> Result<String, String> {
    let mut output = String::new();
    for node in nodes {
        output.push_str(&render_node(node, context)?);
    }
    Ok(output)
}

fn eval_condition(condition: &str, context: &HashMap<String, Value>) -> Result<bool, String> {
    let parts: Vec<&str> = condition.split('.').collect();
    let mut current_value = context.get(parts[0]);

    for &part in &parts[1..] {
        match current_value {
            Some(Value::Object(obj)) => current_value = obj.get(part),
            _ => return Err(format!("Cannot access '{}' in '{}'", part, condition)),
        }
    }

    match current_value {
        Some(Value::Boolean(b)) => Ok(*b),
        Some(Value::Number(n)) => Ok(*n != 0.0),
        Some(Value::String(s)) => Ok(!s.is_empty()),
        Some(Value::List(l)) => Ok(!l.is_empty()),
        Some(Value::Object(o)) => Ok(!o.is_empty()),
        None => Err(format!("Condition '{}' not found in context", condition)),
    }
}

pub struct TemplateEngine {
    pub templates: HashMap<String, Template>,
}

impl TemplateEngine {
    pub fn new() -> Self {
        TemplateEngine {
            templates: HashMap::new(),
        }
    }

    pub fn add_template_from_file(&mut self, name: &str, path: &Path) -> io::Result<()> {
        let content = fs::read_to_string(path)?;
        let template =
            Template::new(&content).map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
        self.templates.insert(name.to_string(), template);
        Ok(())
    }

    pub fn add_template_from_string(&mut self, name: &str, template: &str) -> Result<(), String> {
        let template =
            Template::new(template).map_err(|e| format!("Failed to parse template: {}", e))?;
        self.templates.insert(name.to_string(), template);
        Ok(())
    }

    pub fn render(&self, name: &str, context: &HashMap<String, Value>) -> Result<String, String> {
        match self.templates.get(name) {
            Some(template) => template.render(context),
            None => Err(format!("Template '{}' not found", name)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEMPLATE_NAME: &str = "test";

    fn create_test_engine() -> TemplateEngine {
        let mut engine = TemplateEngine::new();
        let template = r#"<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{{ title }}</title>
</head>
<body>
    <h1>{{ title }}</h1>
    <p>Price: ${{ price }}</p>
    <p>User: {{ user.name }} ({{ user.age }} years old)</p>
    {% if show_message %}
        <p>Welcome to our website!</p>
    {% else %}
        <p>Please log in to see the welcome message.</p>
    {% endif %}
    <h2>Available Items:</h2>
    <ul>
        {% for item in items %}
            <li>{{ item }}</li>
        {% endfor %}
    </ul>
</body>
</html>"#;
        engine
            .add_template_from_string(TEMPLATE_NAME, template)
            .unwrap();
        engine
    }

    fn create_test_context() -> HashMap<String, Value> {
        let mut context = HashMap::new();
        context.insert(
            "title".to_string(),
            Value::String("Welcome to CrabTML!".to_string()),
        );
        context.insert("show_message".to_string(), Value::Boolean(true));
        context.insert(
            "items".to_string(),
            Value::List(vec![
                Value::String("Apple".to_string()),
                Value::String("Banana".to_string()),
                Value::String("Cherry".to_string()),
            ]),
        );
        context.insert("price".to_string(), Value::Number(19.99));

        let mut user_info = HashMap::new();
        user_info.insert("name".to_string(), Value::String("John Doe".to_string()));
        user_info.insert("age".to_string(), Value::Number(30.0));
        context.insert("user".to_string(), Value::Object(user_info));

        context
    }

    #[test]
    fn test_template_rendering() {
        let engine = create_test_engine();
        let context = create_test_context();

        let rendered = engine.render(TEMPLATE_NAME, &context).unwrap();

        assert!(rendered.contains("<title>Welcome to CrabTML!</title>"));
        assert!(rendered.contains("<h1>Welcome to CrabTML!</h1>"));
        assert!(rendered.contains("<p>Price: $19.99</p>"));
        assert!(rendered.contains("<p>User: John Doe (30 years old)</p>"));
        assert!(rendered.contains("<p>Welcome to our website!</p>"));
        assert!(rendered.contains("<li>Apple</li>"));
        assert!(rendered.contains("<li>Banana</li>"));
        assert!(rendered.contains("<li>Cherry</li>"));
    }

    #[test]
    fn test_conditional_rendering() {
        let engine = create_test_engine();
        let mut context = create_test_context();

        // Test with show_message = true
        let rendered = engine.render(TEMPLATE_NAME, &context).unwrap();
        assert!(rendered.contains("<p>Welcome to our website!</p>"));
        assert!(!rendered.contains("<p>Please log in to see the welcome message.</p>"));

        // Test with show_message = false
        context.insert("show_message".to_string(), Value::Boolean(false));
        let rendered = engine.render(TEMPLATE_NAME, &context).unwrap();
        assert!(!rendered.contains("<p>Welcome to our website!</p>"));
        assert!(rendered.contains("<p>Please log in to see the welcome message.</p>"));
    }

    #[test]
    fn test_loop_rendering() {
        let engine = create_test_engine();
        let mut context = create_test_context();

        // Test with existing items
        let rendered = engine.render(TEMPLATE_NAME, &context).unwrap();
        assert!(rendered.contains("<li>Apple</li>"));
        assert!(rendered.contains("<li>Banana</li>"));
        assert!(rendered.contains("<li>Cherry</li>"));

        // Test with empty list
        context.insert("items".to_string(), Value::List(vec![]));
        let rendered = engine.render(TEMPLATE_NAME, &context).unwrap();
        assert!(!rendered.contains("<li>"));
    }

    #[test]
    fn test_nested_object_access() {
        let engine = create_test_engine();
        let context = create_test_context();

        let rendered = engine.render(TEMPLATE_NAME, &context).unwrap();
        assert!(rendered.contains("<p>User: John Doe (30 years old)</p>"));
    }
}
