use elsa::sync::*;

use std::sync::Arc;
use std::thread;

fn main() {
    let a = Arc::new(FrozenMap::new());
    for i in 1..10 {
    let b = a.clone();
        thread::spawn(move || {
            b.insert(i, i.to_string());
            thread::sleep_ms(300);
            loop {
                if let Some(opposite) = b.get(&(10 - i)) {
                    assert!(opposite.parse::<i32>().unwrap() == 10 - i);
                    break;
                } else {
                    thread::sleep_ms(200);

                }
            }
        });
    }

    thread::sleep_ms(1000);
}
