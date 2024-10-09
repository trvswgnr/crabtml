#![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
#![doc = include_str!("../README.md")]

use std::{
    collections::HashMap,
    fmt, fs, io,
    ops::{Deref, DerefMut},
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};

use nom::{
    branch::alt,
    bytes::complete::{tag, take_until, take_while1},
    character::complete::{alphanumeric1, multispace0},
    combinator::map,
    multi::many0,
    sequence::separated_pair,
    sequence::{delimited, preceded, terminated},
    IResult,
};

#[derive(Debug, Clone)]
enum Node {
    Text(String),
    Variable(String),
    If(String, Vec<Node>, Option<Vec<Node>>),
    For(String, String, Vec<Node>),
}

#[derive(Debug, Clone)]
struct Template {
    nodes: Vec<Node>,
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

    pub fn render(&self, context: &Context) -> Result<String, String> {
        render_nodes(&self.nodes, context)
    }
}

/// Represents a simple object that can be used to store key-value pairs.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Object(pub HashMap<String, Value>);

impl Object {
    /// Creates a new `Object`.
    pub fn new() -> Self {
        Object(HashMap::new())
    }

    /// Gets the value associated with the given key.
    pub fn get(&self, key: &str) -> Option<&Value> {
        self.0.get(key)
    }

    /// Sets the value for the given key.
    ///
    /// If the object didn't have this key present, `None` is returned.
    ///
    /// If the object did have this key present, the value is updated, and the
    /// old value is returned. The key should be a string and the value should
    /// be convertible to a `Value`.
    pub fn set<T: Into<String>, V: Into<Value>>(&mut self, key: T, value: V) -> Option<Value> {
        self.0.insert(key.into(), value.into())
    }

    /// Checks if the object is empty, i.e. has no key-value pairs.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the number of key-value pairs in the object.
    pub fn size(&self) -> usize {
        self.0.len()
    }
}

impl FromIterator<(String, Value)> for Object {
    fn from_iter<T: IntoIterator<Item = (String, Value)>>(iter: T) -> Self {
        Object(HashMap::from_iter(iter))
    }
}

/// Represents a context that can be used to store key-value pairs.
///
/// Implements `Deref` and `DerefMut` to allow easy access to the underlying
/// `Object`.
#[derive(Debug, Clone, PartialEq)]
pub struct Context(pub Object);
impl Context {
    /// Creates a new `Context`.
    pub fn new() -> Self {
        Context(Object::new())
    }

    /// Creates a new `Context` from a JSON file.
    pub fn from_file<P: AsRef<Path>>(path: P) -> Result<Self, String> {
        let path = PathBuf::from(path.as_ref());
        // if the file does not exist, return an Error
        if !path.exists() {
            return Err(format!("Context file not found: {}", path.display()));
        }
        // if the file is not a JSON file, return an Error
        if path.extension().unwrap_or_default() != ".json" {
            return Err(format!(
                "Context file is not a JSON file: {}",
                path.display()
            ));
        }
        let content =
            fs::read_to_string(path).map_err(|e| format!("Failed to read context file: {}", e))?;
        let object = serde_json::from_str(&content)
            .map_err(|e| format!("Failed to parse context: {}", e))?;
        Ok(Context(object))
    }
}

impl Deref for Context {
    type Target = Object;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl DerefMut for Context {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// Represents a value that can be used in templates.
///
/// This enum can hold different types of values such as strings, numbers,
/// booleans, lists, and objects.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Value {
    /// A string value.
    String(String),
    /// A number value, represented as a 64-bit floating-point number.
    Number(f64),
    /// A boolean value.
    Boolean(bool),
    /// A list of values.
    List(Vec<Value>),
    /// An object containing key-value pairs.
    Object(Object),
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

    let (input, true_branch, else_branch) =
        match take_until::<_, _, nom::error::Error<&str>>("{% else %}")(input) {
            Ok((remaining, true_content)) => {
                let (remaining, _) = tag("{% else %}")(remaining)?;
                let (remaining, else_content) = take_until("{% endif %}")(remaining)?;
                (remaining, true_content, Some(else_content))
            }
            Err(_) => {
                let (remaining, true_content) = take_until("{% endif %}")(input)?;
                (remaining, true_content, None)
            }
        };

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

fn render_node(node: &Node, context: &Context) -> Result<String, String> {
    match node {
        Node::Text(text) => Ok(text.clone()),
        Node::Variable(name) => {
            let parts: Vec<&str> = name.split('.').collect();
            let mut current_value = context.get(parts[0]);

            for &part in &parts[1..] {
                match current_value {
                    Some(Value::Object(obj)) => current_value = obj.get(part),
                    _ => return Err(format!("Cannot access `{}` in `{}`", part, name)),
                }
            }

            match current_value {
                Some(value) => Ok(value.to_string()),
                None => Err(format!("Variable `{}` not found in context", name)),
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
                        "Collection `{}` not found or not a list",
                        collection
                    ))
                }
            };
            let mut output = String::new();
            for value in items {
                let mut loop_context = context.clone();
                loop_context.set(item.clone(), value.clone());
                output.push_str(&render_nodes(body, &loop_context)?);
            }
            Ok(output)
        }
    }
}

fn render_nodes(nodes: &[Node], context: &Context) -> Result<String, String> {
    let mut output = String::new();
    for node in nodes {
        output.push_str(&render_node(node, context)?);
    }
    Ok(output)
}

fn eval_condition(condition: &str, context: &Context) -> Result<bool, String> {
    let parts: Vec<&str> = condition.split('.').collect();
    let mut current_value = context.get(parts[0]);

    for &part in &parts[1..] {
        match current_value {
            Some(Value::Object(obj)) => current_value = obj.get(part),
            _ => return Err(format!("Cannot access `{}` in `{}`", part, condition)),
        }
    }

    match current_value {
        Some(Value::Boolean(b)) => Ok(*b),
        Some(Value::Number(n)) => Ok(*n != 0.0),
        Some(Value::String(s)) => Ok(!s.is_empty()),
        Some(Value::List(l)) => Ok(!l.is_empty()),
        Some(Value::Object(o)) => Ok(!o.is_empty()),
        None => Err(format!("Condition `{}` not found in context", condition)),
    }
}

/// Represents a template engine.
///
/// # Examples
///
/// ```
/// use crabtml::TemplateEngine;
/// let engine = TemplateEngine::new();
/// ```
pub struct TemplateEngine {
    templates: HashMap<String, Template>,
}

impl TemplateEngine {
    /// Creates a new `TemplateEngine`.
    pub fn new() -> Self {
        TemplateEngine {
            templates: HashMap::new(),
        }
    }

    fn add_template(&mut self, name: &str, template: Template) -> Result<(), io::Error> {
        if self.templates.contains_key(name) {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                format!("Template '{}' has already been added", name),
            ));
        }
        self.templates.insert(name.to_string(), template);
        Ok(())
    }

    /// Adds a template from a file path to the template engine.
    ///
    /// # Examples
    ///
    /// ```
    /// use crabtml::TemplateEngine;
    /// let mut engine = TemplateEngine::new();
    /// engine.add_template_from_file("test1", "tests/test.html").unwrap();
    /// assert!(!engine.is_empty());
    /// ```
    pub fn add_template_from_file<P: AsRef<Path>>(
        &mut self,
        name: &str,
        pathname: P,
    ) -> io::Result<()> {
        let path = PathBuf::from(pathname.as_ref());
        let content = fs::read_to_string(path)?;
        let template =
            Template::new(&content).map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
        self.add_template(name, template)
    }

    /// Adds a template from a string to the template engine.
    ///
    /// # Examples
    ///
    /// ```
    /// use crabtml::TemplateEngine;
    /// let mut engine = TemplateEngine::new();
    /// engine.add_template_from_string("test", "hello {{ text }}").unwrap();
    /// assert!(!engine.is_empty());
    /// ```
    pub fn add_template_from_string(
        &mut self,
        name: &str,
        template: &str,
    ) -> Result<(), io::Error> {
        let template =
            Template::new(template).map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
        self.add_template(name, template)
    }

    /// Renders a template.
    ///
    /// # Examples
    ///
    /// ```
    /// use crabtml::{Context, TemplateEngine};
    ///
    /// let mut engine = TemplateEngine::new();
    /// engine
    ///     .add_template_from_string("test", "hello {{ text }}")
    ///     .unwrap();
    /// let mut context = Context::new();
    /// context.set("text", "darkness my old friend");
    /// let rendered = engine.render("test", &context).unwrap();
    /// assert_eq!(rendered, "hello darkness my old friend");
    /// ```
    pub fn render(&self, name: &str, context: &Context) -> Result<String, String> {
        match self.templates.get(name) {
            Some(template) => template.render(context),
            None => Err(format!("Template '{}' not found", name)),
        }
    }

    /// Checks if the template engine is empty, i.e. has no templates.
    ///
    /// # Examples
    ///
    /// ```
    /// use crabtml::TemplateEngine;
    /// let engine = TemplateEngine::new();
    /// assert!(engine.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.templates.is_empty()
    }
}

/// Creates an `Object` from a list of key-value pairs.
#[macro_export]
macro_rules! object {
    ($($key:expr => $value:expr),* $(,)?) => {{
        let mut object = ::std::collections::HashMap::new();
        $(
            object.insert($key.to_string(), $crate::Value::from($value));
        )*
        $crate::Object(object)
    }};
}

/// Creates a `Context` from a list of key-value pairs.
#[macro_export]
macro_rules! context {
    ($($key:expr => $value:expr),* $(,)?) => {{
        $crate::object!($($key => $value),*)
    }};
}

impl From<&str> for Value {
    fn from(s: &str) -> Self {
        Value::String(s.to_string())
    }
}

impl From<String> for Value {
    fn from(s: String) -> Self {
        Value::String(s)
    }
}

impl From<f64> for Value {
    fn from(n: f64) -> Self {
        Value::Number(n)
    }
}

impl From<i32> for Value {
    fn from(n: i32) -> Self {
        Value::Number(n as f64)
    }
}

impl From<bool> for Value {
    fn from(b: bool) -> Self {
        Value::Boolean(b)
    }
}

impl<T: Into<Value>> From<Vec<T>> for Value {
    fn from(v: Vec<T>) -> Self {
        Value::List(v.into_iter().map(|item| item.into()).collect())
    }
}

impl<T: Into<Value>> From<HashMap<String, T>> for Value {
    fn from(m: HashMap<String, T>) -> Self {
        Value::Object(m.into_iter().map(|(k, v)| (k, v.into())).collect())
    }
}

impl From<Object> for Value {
    fn from(o: Object) -> Self {
        Value::Object(o)
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

    fn create_test_context() -> Context {
        let mut context = Context::new();
        context.set(
            "title".to_string(),
            Value::String("Welcome to CrabTML!".to_string()),
        );
        context.set("show_message".to_string(), Value::Boolean(true));
        context.set(
            "items".to_string(),
            Value::List(vec![
                Value::String("Apple".to_string()),
                Value::String("Banana".to_string()),
                Value::String("Cherry".to_string()),
            ]),
        );
        context.set("price".to_string(), Value::Number(19.99));

        let mut user_info = Object::new();
        user_info.set("name".to_string(), Value::String("John Doe".to_string()));
        user_info.set("age".to_string(), Value::Number(30.0));
        context.set("user".to_string(), Value::Object(user_info));

        context
    }

    #[test]
    fn test_basic_example() {
        let mut engine = TemplateEngine::new();

        // Load a template from a string
        engine
            .add_template_from_string(TEMPLATE_NAME, "hello {{ text }}")
            .unwrap();

        // Create a context
        let mut context = Context::new();
        context.set(
            "text".to_string(),
            Value::String("darkness my old friend".to_string()),
        );

        // Render the template
        let result = engine.render(TEMPLATE_NAME, &context).unwrap();
        assert_eq!(result, "hello darkness my old friend");
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
        context.set("show_message".to_string(), Value::Boolean(false));
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
        context.set("items".to_string(), Value::List(vec![]));
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

    #[test]
    fn test_if_condition_no_else() {
        let mut engine = TemplateEngine::new();
        engine
            .add_template_from_string("no_else", "{% if cond %}hello{% endif %}")
            .unwrap();
        let mut context = Context::new();
        context.set("cond".to_string(), Value::Boolean(true));
        let rendered = engine.render("no_else", &context).unwrap();
        assert_eq!(rendered, "hello");
    }

    #[test]
    fn test_context_macro() {
        let context = context! {
            "title" => "Welcome to CrabTML!",
            "show_message" => true,
            "items" => vec!["Apple", "Banana", "Cherry"],
            "price" => 19.99,
            "user" => context! {
                "name" => "John Doe",
                "age" => 30.0,
            },
        };

        assert_eq!(context.size(), 5);
        assert_eq!(
            context.get("title"),
            Some(&Value::String("Welcome to CrabTML!".to_string()))
        );
        assert_eq!(context.get("show_message"), Some(&Value::Boolean(true)));
        assert_eq!(
            context.get("items"),
            Some(&Value::List(vec![
                Value::String("Apple".to_string()),
                Value::String("Banana".to_string()),
                Value::String("Cherry".to_string()),
            ]))
        );
        assert_eq!(context.get("price"), Some(&Value::Number(19.99)));

        assert!(
            context.get("user").is_some(),
            "User object not found in context"
        );

        if let Some(Value::Object(user)) = context.get("user") {
            assert_eq!(
                user.get("name"),
                Some(&Value::String("John Doe".to_string()))
            );
            assert_eq!(user.get("age"), Some(&Value::Number(30.0)));
        }
    }

    #[test]
    fn test_template_error_handling() {
        let engine = TemplateEngine::new();
        let result = engine.render("test", &Context::new());
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), "Template 'test' not found".to_string());
    }

    #[test]
    fn test_variable_error_handling() {
        let mut engine = TemplateEngine::new();
        engine
            .add_template_from_string("test", "hello {{ text }}")
            .unwrap();
        let result = engine.render("test", &Context::new());
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            "Variable `text` not found in context".to_string()
        );
    }
}
