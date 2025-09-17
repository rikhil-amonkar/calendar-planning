from z3 import *
import json

def main():
    # City indices
    Tallinn = 0
    Bucharest = 1
    Seville = 2
    Stockholm = 3
    Munich = 4
    Milan = 5
    
    city_names = {
        Tallinn: "Tallinn",
        Bucharest: "Bucharest",
        Seville: "Seville",
        Stockholm: "Stockholm",
        Munich: "Munich",
        Milan: "Milan"
    }
    
    # Durations for each city
    durations = [2, 4, 5, 5, 5, 2]
    
    # Direct flights (bidirectional)
    allowed_flights = [
        (Milan, Stockholm), (Stockholm, Milan),
        (Munich, Stockholm), (Stockholm, Munich),
        (Bucharest, Munich), (Munich, Bucharest),
        (Munich, Seville), (Seville, Munich),
        (Stockholm, Tallinn), (Tallinn, Stockholm),
        (Munich, Milan), (Milan, Munich),
        (Munich, Tallinn), (Tallinn, Munich),
        (Seville, Milan), (Milan, Seville)
    ]
    
    s = Solver()
    
    # Order of cities (6 segments)
    order = [Int(f"order_{i}") for i in range(6)]
    for i in range(6):
        s.add(And(order[i] >= 0, order[i] <= 5))
    s.add(Distinct(order))
    
    # Start and end days for each segment
    start = [Int(f"start_{i}") for i in range(6)]
    end = [Int(f"end_{i}") for i in range(6)]
    
    # First segment starts on day 1
    s.add(start[0] == 1)
    
    # Last segment ends on day 18
    s.add(end[5] == 18)
    
    # Create a Z3 array for durations
    duration_array = Array('durations', IntSort(), IntSort())
    for i in range(6):
        s.add(duration_array[i] == durations[i])
    
    # Constraints for each segment
    for i in range(6):
        city = order[i]
        duration = duration_array[city]
        s.add(end[i] == start[i] + duration - 1)
    
    # Consecutive segments start on the same day the previous segment ends
    for i in range(5):
        s.add(start[i+1] == end[i])
    
    # City-specific constraints
    for i in range(6):
        city = order[i]
        # Bucharest between day 1 and 4
        s.add(Implies(city == Bucharest, And(start[i] >= 1, end[i] <= 4)))
        # Seville between day 8 and 12
        s.add(Implies(city == Seville, And(start[i] >= 8, end[i] <= 12)))
        # Munich between day 4 and 8
        s.add(Implies(city == Munich, And(start[i] >= 4, end[i] <= 8)))
    
    # Direct flight constraints between consecutive segments
    for i in range(5):
        city_from = order[i]
        city_to = order[i+1]
        s.add(Or(*[And(city_from == a, city_to == b) for (a, b) in allowed_flights]))
    
    # Check satisfiability
    if s.check() == sat:
        model = s.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(6)]
        start_val = [model.evaluate(start[i]).as_long() for i in range(6)]
        end_val = [model.evaluate(end[i]).as_long() for i in range(6)]
        
        itinerary = []
        for i in range(6):
            city_index = order_val[i]
            city_name = city_names[city_index]
            day_range = f"Day {start_val[i]}-{end_val[i]}"
            itinerary.append({"day_range": day_range, "place": city_name})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()