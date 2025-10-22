#[export_name = "\x01snek_print"]
pub fn snek_print(val : i64) -> i64 {
    println!("snek_print got value: {}", val);
    return val;
}