
def func1(a,b,c)
	func2(a,b) {|a| a}
end

def func2(a,b)
	func3(a) { yield(b) }
end

def func3(a)
	yield();
end

func1(1,2,3)

#answer: 2
