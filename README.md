# Core Rust Small Step Operational Semantics.
#### By Nick Horton
## Rust
Rust is a modern programming language. One of its major goals is memory safety. Rust accomplishes this goal via a meachanism called the borrow checker. The borrow checker is a complex an interesting programming feat, I am going to attempt to explain it simply via mechanisms in C++. 

In C++ there are two kinds of semantics, move and copy semantics. Copy semantics is the default and is used on most objects but importatnly copy semantics are used on raw pointers. A raw pointer is just a memory address, and using that memory address the underlying memory can be read from or written too. Copy semantics says that when that raw pointer is passed to a function, just copy the memory adress for the arguemnt of the function. If the function then invalates the memory address the main program (which still has accesss to reading and writing from the raw pointer) when dereferencing the pointer will cause a segfault. This is a very common bug and move semantics was added in part to make sure this does not happen. Move semantics says that when the raw pointer is passed to a function the variable that is holding said pointer in the main program is removed. So now we say the fucntion has "ownership" of the memory location. Critically if the programmer trys to access this raw pointer after ownership was passed to the function, the program will not compile. So instead of a segmentation fault happening at runtime, the issue presents at compile time. 

This is an oversimplification but in C++ copy semantics are default. In rust shallow copying in this way is not possible and move semantics are default. When you want to pass existing memory to a function there are 4 main ways to accomplish this in Rust.
1. Deep copy the data. For example if you have a array of 1000 elements you can copy all 1000 elements into the function. Obviously the drawback is that this take a lot of time and memory especially if the function is simple.
2. Move the data. Give ownership to the function of the data. This is what is done my default. But what if you still want acces to said data after the function has completed execution?
3. Borrow the data. This means your function can read from the data but not change it in any way.
4. Mutably borrow the data. This means your function can read and write the data.
   
Deep copy / moving the data is often cumbersome and to "extreme" of a measure, but obviosuly it is memory safe. So often programmers choose the borrowing option. The borrow checker has a few rules.

1. You can have multiple borrows or one mutable borrow.
2. Borrows have a lifetime that is not obvious but once it is dead. The outerscope can read and write to the data again.

## Small Step Semantics for Rust
The goal is to build up the 

## References

