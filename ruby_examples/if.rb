
def func1(a,b,c)
	func2(a,b) {|a| return a}
end

def func2(a,b)
	func3(true) { |a| 
				if a 
			      return yield(b + 12) + 2
   				else
				  b
				end	}
    b +	5
end

def func3(a)
	yield(a,2,3);
end


func1(1,2,3)

#answer: 3
