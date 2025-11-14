#[export_name = "\x01snek_print"]
pub fn snek_print(val : i64) -> i64 {
    if (val % 2) == 0  {
        println!("{}", val / 2);
    }
    else if  val == 3  {
        println!("true");
    }
    else if  val == 1  {
        println!("false");
    }
    else {
        panic!("Invalid value: {}", val);
    }
    return val;
}



#[export_name = "\x01snek_err"]
pub fn snek_err(code : i64, val1 : i64, val2 : i64) -> i64 {
    let err = match code {
        1 => "invalid argument",
        2 => "overflow",
        _ => "unknown error",
    };
    eprintln!("error {}: {} {}", err, val1, val2);
    panic!("snek_error");
}
