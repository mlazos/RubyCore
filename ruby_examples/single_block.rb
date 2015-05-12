#simple block call

def func1(a,c)
	func2(a) { return c }	
end

def func2(a)
	yield(a)
	a = 1
end

func1(1,2)
#answer 2
