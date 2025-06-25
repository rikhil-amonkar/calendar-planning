from z3 import *

def main():
    # Define the city enumeration
    City = Datatype('City')
    City.declare('Split')
    City.declare('London')
    City.declare('Santorini')
    City = City.create()
    
    # Variables for segments
    s1, e1 = Int('s1'), Int('e1')
    s2, e2 = Int('s2'), Int('e2')
    s3, e3 = Int('s3'), Int('e3')
    city1, city2, city3 = Consts('city1 city2 city3', City)
    
    s = Solver()
    
    # Constraints on segment boundaries
    s.add(s1 == 1)
    s.add(s2 == e1)
    s.add(s3 == e2)
    s.add(e3 == 18)
    
    # Ensure segments are within valid day ranges and non-empty
    s.add(e1 >= s1, e1 <= 18)
    s.add(e2 >= s2, e2 <= 18)
    s.add(e3 >= s3, e3 <= 18)
    
    # Calculate days per city
    split_days = Sum([If(city1 == City.Split, e1 - s1 + 1, 0),
                     If(city2 == City.Split, e2 - s2 + 1, 0),
                     If(city3 == City.Split, e3 - s3 + 1, 0)])
    london_days = Sum([If(city1 == City.London, e1 - s1 + 1, 0),
                       If(city2 == City.London, e2 - s2 + 1, 0),
                       If(city3 == City.London, e3 - s3 + 1, 0)])
    santorini_days = Sum([If(city1 == City.Santorini, e1 - s1 + 1, 0),
                          If(city2 == City.Santorini, e2 - s2 + 1, 0),
                          If(city3 == City.Santorini, e3 - s3 + 1, 0)])
    
    s.add(split_days == 6)
    s.add(london_days == 7)
    s.add(santorini_days == 7)
    
    # Flight connection constraints
    s.add(Or(
        And(city1 == City.Split, city2 == City.London),
        And(city1 == City.London, city2 == City.Split),
        And(city1 == City.London, city2 == City.Santorini),
        And(city1 == City.Santorini, city2 == City.London)
    ))
    s.add(Or(
        And(city2 == City.Split, city3 == City.London),
        And(city2 == City.London, city3 == City.Split),
        And(city2 == City.London, city3 == City.Santorini),
        And(city2 == City.Santorini, city3 == City.London)
    ))
    
    # Last segment must be in Santorini
    s.add(city3 == City.Santorini)
    
    # Ensure day 12 is in Santorini
    in_santorini_day12 = Or(
        And(city1 == City.Santorini, s1 <= 12, 12 <= e1),
        And(city2 == City.Santorini, s2 <= 12, 12 <= e2),
        And(city3 == City.Santorini, s3 <= 12, 12 <= e3)
    )
    s.add(in_santorini_day12)
    
    # Consecutive segments must be in different cities
    s.add(city1 != city2, city2 != city3)
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        s1_val = m[s1].as_long()
        e1_val = m[e1].as_long()
        s2_val = m[s2].as_long()
        e2_val = m[e2].as_long()
        s3_val = m[s3].as_long()
        e3_val = m[e3].as_long()
        
        city_map = {
            City.Split: "Split",
            City.London: "London",
            City.Santorini: "Santorini"
        }
        city1_val = m[city1]
        city2_val = m[city2]
        city3_val = m[city3]
        
        itinerary = [
            {"day_range": f"Day {s1_val}-{e1_val}", "place": city_map[city1_val]},
            {"day_range": f"Day {e1_val}", "place": city_map[city1_val]},
            {"day_range": f"Day {e1_val}", "place": city_map[city2_val]},
            {"day_range": f"Day {s2_val}-{e2_val}", "place": city_map[city2_val]},
            {"day_range": f"Day {e2_val}", "place": city_map[city2_val]},
            {"day_range": f"Day {e2_val}", "place": city_map[city3_val]},
            {"day_range": f"Day {s3_val}-{e3_val}", "place": city_map[city3_val]}
        ]
        
        result = {"itinerary": itinerary}
        print(f"result = {result}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()