
def func1(a,b,c)
	func2(a,b) {|a| a}
end

def func2(a,b)
	func3(a) { |a| yield(b + a) }
end

def func3(a)
	yield(a,2,3);
end


func1(1,2,3)

#answer: 3
