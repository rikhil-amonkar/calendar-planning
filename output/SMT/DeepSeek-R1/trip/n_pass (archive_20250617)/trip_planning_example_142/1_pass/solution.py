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
    
    # Function to check if a city is visited on a given day
    def is_city_visited(day_index, city):
        # If the day starts in the city or travels and ends in the city
        return Or(
            start[day_index] == city,
            And(start[day_index] != end[day_index], end[day_index] == city)
        )
    
    # Lists to track visits per city
    madrid_days = [is_city_visited(i, Madrid) for i in range(num_days)]
    dublin_days = [is_city_visited(i, Dublin) for i in range(num_days)]
    tallinn_days = [is_city_visited(i, Tallinn) for i in range(num_days)]
    
    # Constraint: Total days in each city
    s.add(Sum([If(day, 1, 0) for day in madrid_days]) == 4)
    s.add(Sum([If(day, 1, 0) for day in dublin_days]) == 3)
    s.add(Sum([If(day, 1, 0) for day in tallinn_days]) == 2)
    
    # Constraint: Must be in Tallinn on days 6 and 7 (indices 5 and 6)
    s.add(tallinn_days[5])
    s.add(tallinn_days[6])
    
    # Solve the problem
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