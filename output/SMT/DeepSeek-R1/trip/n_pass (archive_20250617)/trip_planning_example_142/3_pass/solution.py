from z3 import *

def main():
    s = Solver()
    
    # City representations
    Madrid = 0
    Dublin = 1
    Tallinn = 2
    cities = ['Madrid', 'Dublin', 'Tallinn']
    num_days = 7  # 7 days: day0 to day6
    
    # Start city for day0
    start_city = Int('start_city')
    s.add(Or(start_city == Madrid, start_city == Dublin, start_city == Tallinn))
    
    # End city for each day
    end_city = [Int('end_%d' % i) for i in range(num_days)]
    for i in range(num_days):
        s.add(Or(end_city[i] == Madrid, end_city[i] == Dublin, end_city[i] == Tallinn))
    
    # Flight constraints
    for i in range(num_days):
        if i == 0:
            start_i = start_city
        else:
            start_i = end_city[i-1]
        end_i = end_city[i]
        s.add(Or(
            start_i == end_i,
            And(start_i == Madrid, end_i == Dublin),
            And(start_i == Dublin, end_i == Madrid),
            And(start_i == Dublin, end_i == Tallinn),
            And(start_i == Tallinn, end_i == Dublin)
        ))
    
    # Count days in each city
    def is_visited(day, city):
        if day == 0:
            start_day = start_city
        else:
            start_day = end_city[day-1]
        end_day = end_city[day]
        return Or(start_day == city, end_day == city)
    
    madrid_days = [is_visited(i, Madrid) for i in range(num_days)]
    dublin_days = [is_visited(i, Dublin) for i in range(num_days)]
    tallinn_days = [is_visited(i, Tallinn) for i in range(num_days)]
    
    s.add(Sum([If(day, 1, 0) for day in madrid_days]) == 4)
    s.add(Sum([If(day, 1, 0) for day in dublin_days]) == 3)
    s.add(Sum([If(day, 1, 0) for day in tallinn_days]) == 2)
    
    # Workshop in Tallinn on days 6 and 7 (indices 5 and 6)
    s.add(is_visited(5, Tallinn))
    s.add(is_visited(6, Tallinn))
    
    # Solve and print
    if s.check() == sat:
        model = s.model()
        start_val = model.evaluate(start_city).as_long()
        end_vals = [model.evaluate(end_city[i]).as_long() for i in range(num_days)]
        
        print("Day\tStart\t\tEnd")
        for i in range(num_days):
            if i == 0:
                start_city_val = start_val
            else:
                start_city_val = end_vals[i-1]
            end_city_val = end_vals[i]
            print(f"{i+1}\t{cities[start_city_val]}\t{cities[end_city_val]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()