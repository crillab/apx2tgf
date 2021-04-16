# Crusti_arg

Crusti_arg is a library and an app used to handle Argumentation Frameworks.

# Abstract Argument Frameworks

This library allows to handle Abstract Argumentation Frameworks through the `AAFramework` struct.

In order to create an AAF, you must provide its argument set, which is itself built upon the labels of the set of arguments.
Any type following the `LabelType` trait may be used to build an argument set.
When the AAF is built, you can then add attacks to it.

```rust
let labels = vec!["a".to_string(), "b".to_string(), "c".to_string()];
let arguments = ArgumentSet::new(&labels);
let mut framework = AAFramework::new(arguments);
assert_eq!(3, framework.argument_set().len());
assert_eq!(0, framework.iter_attacks().count());
framework.new_attack(&labels[0], &labels[1]);
assert_eq!(1, framework.iter_attacks().count());
```

# Reading and writing AAF

The library provides structures to read and write AAFs, taking advantage of [the Aspartix format](https://www.dbai.tuwien.ac.at/research/argumentation/aspartix/dung.html).

Use the `AspartixReader` to read an AAF from a reader (the label type will be `String`).

```rust
fn read_af_from_str(s: &str) -> AAFramework<String> {
    let reader = AspartixReader::default();
    reader.read(&mut s.as_bytes()).expect("invalid Aspartix AF")
}
```

Use the `AspartixWriter` to write an AAF using the provided writer.

```rust
fn write_af_to_stdout<T: LabelType>(af: &AAFramework<T>) -> Result<()> {
    let writer = AspartixWriter::default();
    writer.write(&af, &mut std::io::stdout())
}
```

# License

Crusti_binnet is developed at CRIL (Centre de Recherche en Informatique de Lens).
It is made available under the terms of the GNU GPLv3 license.