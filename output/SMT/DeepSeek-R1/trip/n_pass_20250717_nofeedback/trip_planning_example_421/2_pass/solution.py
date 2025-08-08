from z3 import *

def main():
    s = Solver()
    
    # Four stays: cities and start days
    cities = [String(f"c{i}") for i in range(4)]
    starts = [Int(f"s{i}") for i in range(4)]
    ends = [Int(f"e{i}") for i in range(4)]
    
    # Days array: maps city name to stay duration
    days_arr = Array('days_arr', StringSort(), IntSort())
    s.add(days_arr["City1"] == 3)
    s.add(days_arr["City2"] == 4)
    s.add(days_arr["City3"] == 2)
    s.add(days_arr["City4"] == 5)
    
    # Cities must be distinct and one of the four
    s.add(Distinct(cities))
    for i in range(4):
        s.add(Or(cities[i] == "City1", cities[i] == "City2", cities[i] == "City3", cities[i] == "City4"))
    
    # Start days are strictly increasing
    s.add(starts[0] == 1)
    s.add(starts[0] < starts[1])
    s.add(starts[1] < starts[2])
    s.add(starts[2] < starts[3])
    
    # First stay is City1, last stay is City4
    s.add(cities[0] == "City1")
    s.add(cities[3] == "City4")
    
    # End days for each stay
    for i in range(4):
        s.add(ends[i] == starts[i] + days_arr[cities[i]] - 1)
    
    # Non-overlapping: end of stay i must be before start of stay i+1
    for i in range(3):
        s.add(ends[i] < starts[i+1])
    
    # Entire trip ends by day 14
    s.add(ends[3] <= 14)
    
    # City2's stay must start on day 5
    for i in range(4):
        s.add(If(cities[i] == "City2", starts[i] == 5, True))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Print the schedule
        print("Found a solution:")
        for i in range(4):
            city = m[cities[i]]
            start = m[starts[i]]
            end = m[ends[i]]
            print(f"Stay {i+1}: City {city}, from day {start} to day {end}")
    else:
        print("unsat")

if __name__ == "__main__":
    main()