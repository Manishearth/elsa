use elsa::FrozenVec;

fn main() {
    let arena = Arena::new();
    let lonely = arena.add_thing("lonely", vec![]);
    let best_friend = arena.add_thing("best friend", vec![lonely]);
    let threes_a_crowd = arena.add_thing("threes a crowd", vec![lonely, best_friend]);
    let rando = arena.add_thing("rando", vec![]);
    let _facebook = arena.add_thing("facebook", vec![rando, threes_a_crowd, lonely, best_friend]);
    arena.dump();
}


struct Arena<'arena> {
    things: FrozenVec<Box<Thing<'arena>>>,
}

struct Thing<'arena> {
    pub friends: FrozenVec<ThingRef<'arena>>,
    pub reverse_friends: FrozenVec<ThingRef<'arena>>,
    pub name: &'static str,
}

type ThingRef<'arena> = &'arena Thing<'arena>;


impl<'arena> Arena<'arena> {
    fn new() -> Arena<'arena> {
        Arena {
            things: FrozenVec::new(),
        }
    }
    
    fn add_thing(&'arena self, name: &'static str, friends: Vec<ThingRef<'arena>>) -> ThingRef<'arena> {
        let idx = self.things.len();
        self.things.push(Box::new(Thing {
            name,
            friends: friends.into(),
            reverse_friends: Default::default(),
        }));
        let me = &self.things[idx];
        for friend in &me.friends {
            friend.reverse_friends.push(me)
        }
        me
    }

    fn dump(&'arena self) {
        for thing in &self.things {
            println!("friends of {}:", thing.name);
            println!("\tdirect friends:");
            for friend in &thing.friends {
                println!("\t\t{}", friend.name);
            }
            println!("\treverse friends:");
            for friend in &thing.reverse_friends {
                println!("\t\t{}", friend.name);
            }
        }
    }
}

// Note that the following will cause the above code to stop compiling
// since non-eyepatched custom destructors can potentially
// read deallocated data.
//
// impl<'arena> Drop for Thing<'arena> {
//     fn drop(&mut self) {
//         println!("goodbye {:?}", self.name);
//         for friend in &self.friends {
//             println!("\t\t{}", friend.name);
//         }
//     }
// }
