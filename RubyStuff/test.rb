#block example

def block_ex(a)
	yield(a)
end

def func(a)
	x = Proc.new {|a| return a}
   	return x.call(a) + 1
end



#proc example

def proc_ex(a, p) 
	p.call(a)
	return "hey"	
end





#lambda example

def func3(a)
	func2(a) {|a| return a} + a
end

def func2(a)
	Proc.new {|a| yield(a + 1) + 1}.call(a)
end

def func1(a)
	yield(a)
end


def two_times
	x = 5
	yield
	yield
end


