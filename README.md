# CrabTML: A Rust-based Template Engine

CrabTML is a lightweight and flexible template engine written in Rust. It provides a simple yet powerful way to render dynamic content in your applications.

> [!WARNING]  
> This project is still in early development and is not recommended for production use.

## Features

- Variable interpolation
- Conditional rendering
- Loop constructs
- Nested object access
- File-based and string-based template loading
- Easy-to-use API

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
crabtml = "0.1.0"
```

## Usage

Here's a quick example of how to use CrabTML:

```rust
use crabtml::{TemplateEngine, Value};
use std::collections::HashMap;

fn main() {
    let mut engine = TemplateEngine::new();
    
    // Load a template from a string
    engine.add_template_from_string("example", "Hello, {{ name }}!").unwrap();
    
    // Create a context
    let mut context = HashMap::new();
    context.insert("name".to_string(), Value::String("World".to_string()));
    
    // Render the template
    let result = engine.render("example", &context).unwrap();
    println!("{}", result); // Output: Hello, World!
}
```

For more detailed examples, check the [`tests` module]((https://github.com/trvswgnr/crabtml/blob/main/src/lib.rs#L239:L361)) in the source code.

## Template Syntax

CrabTML supports the following syntax:

- Variables: `{{ variable_name }}`
- Conditionals: `{% if condition %} ... {% else %} ... {% endif %}`
- Loops: `{% for item in items %} ... {% endfor %}`
- Nested object access: `{{ user.name }}`

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.

## License

This project is licensed under the MIT License - see the LICENSE file for details.