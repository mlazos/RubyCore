#lambda example

def func3(a,b)
	func2(a) {|a| return a} + a
end

def func2(a)
	x = 1;
	Proc.new {|a| yield(a + 1) + [1,2]}.call(a)
end

def func1(a)
	yield(a)
end


x = 1;
func3(5,3)
