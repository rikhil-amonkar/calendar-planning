from z3 import *
import json

def main():
    # Define city enum
    City = Datatype('City')
    City.declare('Dublin')
    City.declare('Riga')
    City.declare('Vilnius')
    City = City.create()
    
    s = Solver()
    
    # City visit order variables
    city1 = Const('city1', City)
    city2 = Const('city2', City)
    city3 = Const('city3', City)
    
    # Duration variables for each stay
    d1 = Int('d1')
    d2 = Int('d2')
    d3 = Int('d3')
    
    # Constraints
    s.add(d1 >= 1, d2 >= 1, d3 >= 1)
    s.add(d1 + d2 + d3 - 2 == 12)  # Account for 2 travel days
    
    # Required days per city
    s.add(If(city1 == City.Dublin, d1 == 2, True))
    s.add(If(city1 == City.Riga, d1 == 5, True))
    s.add(If(city1 == City.Vilnius, d1 == 7, True))
    
    s.add(If(city2 == City.Dublin, d2 == 2, True))
    s.add(If(city2 == City.Riga, d2 == 5, True))
    s.add(If(city2 == City.Vilnius, d2 == 7, True))
    
    s.add(If(city3 == City.Dublin, d3 == 2, True))
    s.add(If(city3 == City.Riga, d3 == 5, True))
    s.add(If(city3 == City.Vilnius, d3 == 7, True))
    
    s.add(Distinct(city1, city2, city3))
    
    # Flight connections
    allowed_flights = [
        (City.Dublin, City.Riga),
        (City.Riga, City.Dublin),
        (City.Riga, City.Vilnius)
    ]
    
    s.add(Or([And(city1 == c1, city2 == c2) for (c1, c2) in allowed_flights]))
    s.add(Or([And(city2 == c1, city3 == c2) for (c1, c2) in allowed_flights]))
    
    if s.check() == sat:
        m = s.model()
        c1 = m[city1]
        c2 = m[city2]
        c3 = m[city3]
        dur1 = m[d1].as_long()
        dur2 = m[d2].as_long()
        dur3 = m[d3].as_long()
        
        # Calculate day ranges
        start1 = 1
        end1 = dur1
        start2 = end1
        end2 = start2 + dur2 - 1
        start3 = end2
        end3 = start3 + dur3 - 1
        
        city_names = {
            City.Dublin: "Dublin",
            City.Riga: "Riga",
            City.Vilnius: "Vilnius"
        }
        
        itinerary = [
            {"day_range": f"Day {start1}-{end1}", "place": city_names[c1]},
            {"day_range": f"Day {start2}-{end2}", "place": city_names[c2]},
            {"day_range": f"Day {start3}-{end3}", "place": city_names[c3]}
        ]
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()