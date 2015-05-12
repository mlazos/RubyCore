y = 2;

def two_times()
	x = 5
	yield
	yield
end

two_times() { y = y + 1 }

y

#answer: 4
