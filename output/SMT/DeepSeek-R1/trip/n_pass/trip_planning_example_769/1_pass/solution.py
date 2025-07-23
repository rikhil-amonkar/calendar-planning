from z3 import *
import json

def main():
    # Define city names and their indices
    cities = ['Porto', 'Prague', 'Reykjavik', 'Santorini', 'Amsterdam', 'Munich']
    n_cities = len(cities)
    
    # Map city names to indices for clarity
    Porto, Prague, Reykjavik, Santorini, Amsterdam, Munich = range(n_cities)
    
    # Direct flight pairs (undirected)
    flight_pairs = [
        (Amsterdam, Porto),
        (Amsterdam, Munich),
        (Amsterdam, Reykjavik),
        (Munich, Porto),
        (Prague, Reykjavik),
        (Munich, Reykjavik),
        (Amsterdam, Santorini),
        (Amsterdam, Prague),
        (Munich, Prague)
    ]
    
    # Initialize Z3 variables
    s0 = Int('s0')
    end = [Int(f'end_{i}') for i in range(16)]  # end[0] is end of day1, ..., end[15] is end of day16
    
    s = Solver()
    
    # Domain constraints for s0 and end variables
    s.add(s0 >= 0, s0 < n_cities)
    for i in range(16):
        s.add(end[i] >= 0, end[i] < n_cities)
    
    # Flight constraints for each day
    for day_index in range(16):  # day_index from 0 to 15, representing day (day_index+1)
        if day_index == 0:
            start_i = s0
        else:
            start_i = end[day_index-1]
        end_i = end[day_index]
        
        # If start_i and end_i are different, ensure there is a direct flight
        if flight_pairs:
            flight_cond = Or([Or(And(start_i == a, end_i == b), And(start_i == b, end_i == a)) for (a, b) in flight_pairs])
            s.add(If(start_i != end_i, flight_cond, True))
    
    # Total days per city
    total_days = [0] * n_cities
    for c in range(n_cities):
        count_start = 0
        count_end_only = 0
        for day_index in range(16):
            if day_index == 0:
                start_i = s0
            else:
                start_i = end[day_index-1]
            end_i = end[day_index]
            
            count_start += If(start_i == c, 1, 0)
            count_end_only += If(And(end_i == c, start_i != c), 1, 0)
        total_days[c] = count_start + count_end_only
    
    # Set total days constraints
    s.add(total_days[Porto] == 5)
    s.add(total_days[Prague] == 4)
    s.add(total_days[Reykjavik] == 4)
    s.add(total_days[Santorini] == 2)
    s.add(total_days[Amsterdam] == 2)
    s.add(total_days[Munich] == 4)
    
    # Event constraints
    # Wedding in Reykjavik between day4 and day7 (days 4,5,6,7)
    wedding_days = [
        Or(end[2] == Reykjavik, end[3] == Reykjavik),  # Day4: start=end[2], end=end[3]
        Or(end[3] == Reykjavik, end[4] == Reykjavik),  # Day5: start=end[3], end=end[4]
        Or(end[4] == Reykjavik, end[5] == Reykjavik),  # Day6: start=end[4], end=end[5]
        Or(end[5] == Reykjavik, end[6] == Reykjavik)   # Day7: start=end[5], end=end[6]
    ]
    s.add(Or(wedding_days))
    
    # Conference in Amsterdam: start of day14 must be Amsterdam, end of day15 must be Amsterdam
    # Day14 start = end[12] (end of day13), Day15 end = end[14] (end of day15)
    s.add(And(end[12] == Amsterdam, end[14] == Amsterdam))
    
    # Meeting in Munich between day7 and day10 (days 7,8,9,10)
    meeting_days = [
        Or(end[5] == Munich, end[6] == Munich),  # Day7: start=end[5], end=end[6]
        Or(end[6] == Munich, end[7] == Munich),  # Day8: start=end[6], end=end[7]
        Or(end[7] == Munich, end[8] == Munich),  # Day9: start=end[7], end=end[8]
        Or(end[8] == Munich, end[9] == Munich)   # Day10: start=end[8], end=end[9]
    ]
    s.add(Or(meeting_days))
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        s0_val = m.eval(s0).as_long()
        end_vals = [m.eval(end[i]).as_long() for i in range(16)]
        
        # Build itinerary: for each day, the end city is the city at the end of the day
        itinerary = []
        for day in range(1, 17):
            city_index = end_vals[day-1]
            city_name = cities[city_index]
            itinerary.append({"day": day, "city": city_name})
        
        # Output the itinerary as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()