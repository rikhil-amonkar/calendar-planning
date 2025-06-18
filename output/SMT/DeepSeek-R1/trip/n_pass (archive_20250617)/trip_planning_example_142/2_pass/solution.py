from z3 import *

def main():
    s = Solver()
    
    # City representations: 0 = Madrid, 1 = Dublin, 2 = Tallinn
    Madrid = 0
    Dublin = 1
    Tallinn = 2
    cities = ['Madrid', 'Dublin', 'Tallinn']
    num_days = 7
    
    # Start and end city for each day
    start = [Int('start_%d' % i) for i in range(num_days)]
    end = [Int('end_%d' % i) for i in range(num_days)]
    
    # Constraint: Start and end must be valid cities (0, 1, or 2)
    for i in range(num_days):
        s.add(Or(start[i] == Madrid, start[i] == Dublin, start[i] == Tallinn))
        s.add(Or(end[i] == Madrid, end[i] == Dublin, end[i] == Tallinn))
    
    # Constraint: The end of day i is the start of day i+1 for i=0 to 5
    for i in range(num_days - 1):
        s.add(end[i] == start[i + 1])
    
    # Constraint: Direct flights only between Madrid-Dublin and Dublin-Tallinn
    for i in range(num_days):
        s.add(Or(
            start[i] == end[i],  # Staying in the same city
            And(start[i] == Madrid, end[i] == Dublin),  # Madrid to Dublin
            And(start[i] == Dublin, end[i] == Madrid),  # Dublin to Madrid
            And(start[i] == Dublin, end[i] == Tallinn),  # Dublin to Tallinn
            And(start[i] == Tallinn, end[i] == Dublin)   # Tallinn to Dublin
        ))
    
    # Count days in each city (a day counts if: start in city OR travel ends in city)
    madrid_days = [Bool('madrid_%d' % i) for i in range(num_days)]
    dublin_days = [Bool('dublin_%d' % i) for i in range(num_days)]
    tallinn_days = [Bool('tallinn_%d' % i) for i in range(num_days)]
    
    for i in range(num_days):
        s.add(madrid_days[i] == Or(start[i] == Madrid, And(start[i] != end[i], end[i] == Madrid)))
        s.add(dublin_days[i] == Or(start[i] == Dublin, And(start[i] != end[i], end[i] == Dublin)))
        s.add(tallinn_days[i] == Or(start[i] == Tallinn, And(start[i] != end[i], end[i] == Tallinn)))
    
    # Total days per city
    s.add(sum([If(madrid_days[i], 1, 0) for i in range(num_days)]) == 4)
    s.add(sum([If(dublin_days[i], 1, 0) for i in range(num_days)]) == 3)
    s.add(sum([If(tallinn_days[i], 1, 0) for i in range(num_days)]) == 2)
    
    # Workshop in Tallinn on days 6 and 7 (index 5 and 6)
    s.add(tallinn_days[5] == True)  # Day 6
    s.add(tallinn_days[6] == True)  # Day 7
    
    # Solve and print schedule
    if s.check() == sat:
        model = s.model()
        start_vals = [model.evaluate(start[i]).as_long() for i in range(num_days)]
        end_vals = [model.evaluate(end[i]).as_long() for i in range(num_days)]
        
        print("Day\tStart\t\tEnd")
        for i in range(num_days):
            start_city = cities[start_vals[i]]
            end_city = cities[end_vals[i]]
            print(f"{i+1}\t{start_city}\t{end_city}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()