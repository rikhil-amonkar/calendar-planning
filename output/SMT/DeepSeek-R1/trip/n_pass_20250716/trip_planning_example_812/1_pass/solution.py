from z3 import *

def main():
    # Define the fixed cities in the sequence
    fixed_sequence = {
        0: "Porto",
        4: "Warsaw",
        6: "Vienna"
    }
    
    # Remaining cities to assign to positions 1, 2, 3, 5
    remaining_cities = ["Paris", "Florence", "Munich", "Nice"]
    
    # Required days for each city
    req_days_dict = {
        "Porto": 3,
        "Paris": 5,
        "Florence": 3,
        "Munich": 5,
        "Warsaw": 3,
        "Nice": 5,
        "Vienna": 2
    }
    
    # Define the direct flights (as an undirected graph by including both directions)
    direct_flights = [
        ("Florence", "Vienna"),
        ("Paris", "Warsaw"),
        ("Munich", "Vienna"),
        ("Porto", "Vienna"),
        ("Warsaw", "Vienna"),
        ("Florence", "Munich"),
        ("Munich", "Warsaw"),
        ("Munich", "Nice"),
        ("Paris", "Florence"),
        ("Warsaw", "Nice"),
        ("Porto", "Munich"),
        ("Porto", "Nice"),
        ("Paris", "Vienna"),
        ("Nice", "Vienna"),
        ("Porto", "Paris"),
        ("Paris", "Nice"),
        ("Paris", "Munich"),
        ("Porto", "Warsaw")
    ]
    symmetric_direct_flights = set()
    for u, v in direct_flights:
        symmetric_direct_flights.add((u, v))
        symmetric_direct_flights.add((v, u))
    
    # Create Z3 string variables for the positions 1, 2, 3, 5
    c1 = String("c1")
    c2 = String("c2")
    c3 = String("c3")
    c5 = String("c5")
    
    s = Solver()
    
    # All variables must be one of the remaining cities and distinct
    s.add(Distinct(c1, c2, c3, c5))
    for var in [c1, c2, c3, c5]:
        s.add(Or([var == StringVal(city) for city in remaining_cities]))
    
    # Define a function to get required days for a city
    def req_days(city):
        return If(city == StringVal("Paris"), 5,
                 If(city == StringVal("Florence"), 3,
                  If(city == StringVal("Munich"), 5,
                   If(city == StringVal("Nice"), 5, 0))))
    
    # Day calculation constraints
    e0 = 3
    e1 = req_days(c1) + 2
    e2 = req_days(c2) + e1 - 1
    e3 = req_days(c3) + e2 - 1
    s.add(e3 == 13)
    
    # Flight constraints: consecutive cities must have direct flights
    def adjacent(city1, city2):
        options = []
        for (u, v) in symmetric_direct_flights:
            options.append(And(city1 == StringVal(u), city2 == StringVal(v)))
        return Or(options)
    
    s.add(adjacent(StringVal("Porto"), c1))
    s.add(adjacent(c1, c2))
    s.add(adjacent(c2, c3))
    s.add(adjacent(c3, StringVal("Warsaw")))
    s.add(adjacent(StringVal("Warsaw"), c5))
    s.add(adjacent(c5, StringVal("Vienna")))
    
    # The city at position 5 must require 5 days
    s.add(req_days(c5) == 5)
    
    if s.check() == sat:
        m = s.model()
        c1_val = str(m.eval(c1))
        c2_val = str(m.eval(c2))
        c3_val = str(m.eval(c3))
        c5_val = str(m.eval(c5))
        
        # Build the sequence
        sequence = [
            "Porto",
            c1_val,
            c2_val,
            c3_val,
            "Warsaw",
            c5_val,
            "Vienna"
        ]
        
        # Calculate start and end days for each segment
        starts = [0] * 7
        ends = [0] * 7
        
        starts[0] = 1
        ends[0] = starts[0] + req_days_dict[sequence[0]] - 1
        
        for i in range(1, 7):
            starts[i] = ends[i-1]
            ends[i] = starts[i] + req_days_dict[sequence[i]] - 1
        
        # Build itinerary
        itinerary = []
        for i in range(7):
            seg_city = sequence[i]
            start = starts[i]
            end = ends[i]
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range_str, "place": seg_city})
            
            if i < 6:
                flight_day = end
                itinerary.append({"day_range": f"Day {flight_day}", "place": seg_city})
                itinerary.append({"day_range": f"Day {flight_day}", "place": sequence[i+1]})
        
        result = {"itinerary": itinerary}
        print(f"result = {result}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()