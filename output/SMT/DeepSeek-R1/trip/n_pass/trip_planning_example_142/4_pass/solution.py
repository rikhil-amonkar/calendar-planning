from z3 import *

def main():
    s = Solver()
    
    # City representations
    Madrid = 0
    Dublin = 1
    Tallinn = 2
    cities = ['Madrid', 'Dublin', 'Tallinn']
    num_days = 7
    
    # Start city for day 1
    start = Int('start')
    s.add(Or(start == Madrid, start == Dublin, start == Tallinn))
    
    # End city for each day
    end = [Int(f'end_{i}') for i in range(num_days)]
    for i in range(num_days):
        s.add(Or(end[i] == Madrid, end[i] == Dublin, end[i] == Tallinn))
    
    # Flight constraints between consecutive days
    for i in range(num_days):
        current_start = start if i == 0 else end[i-1]
        s.add(Or(
            current_start == end[i],  # Stay in same city
            And(current_start == Madrid, end[i] == Dublin),
            And(current_start == Dublin, end[i] == Madrid),
            And(current_start == Dublin, end[i] == Tallinn),
            And(current_start == Tallinn, end[i] == Dublin)
        ))
    
    # Count days in each city (city is counted if present at start or end)
    def in_city(day, city):
        start_city = start if day == 0 else end[day-1]
        end_city = end[day]
        return Or(start_city == city, end_city == city)
    
    # Total days per city
    s.add(Sum([If(in_city(i, Madrid), 1, 0) for i in range(num_days)]) == 4)
    s.add(Sum([If(in_city(i, Dublin), 1, 0) for i in range(num_days)]) == 3)
    s.add(Sum([If(in_city(i, Tallinn), 1, 0) for i in range(num_days)]) == 2)
    
    # Workshop constraints - in Tallinn all of days 6 and 7
    s.add(end[5] == Tallinn)  # End of day 6 is Tallinn
    s.add(end[6] == Tallinn)  # End of day 7 is Tallinn
    s.add(end[4] == Tallinn)  # Start of day 6 is Tallinn (end of day 5)
    
    # Solve and print
    if s.check() == sat:
        m = s.model()
        start_val = m.evaluate(start).as_long()
        end_vals = [m.evaluate(end[i]).as_long() for i in range(num_days)]
        
        print("Day\tStart\t\tEnd")
        # Day 1
        print(f"1\t{cities[start_val]}\t{cities[end_vals[0]]}")
        # Days 2-7
        for i in range(1, num_days):
            start_city = cities[end_vals[i-1]]
            print(f"{i+1}\t{start_city}\t{cities[end_vals[i]]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()