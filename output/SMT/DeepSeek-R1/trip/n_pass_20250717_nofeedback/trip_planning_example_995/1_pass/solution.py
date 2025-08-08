from z3 import *
import json

def main():
    # Define the City enum
    City = Datatype('City')
    City.declare('Barcelona')
    City.declare('Oslo')
    City.declare('Stuttgart')
    City.declare('Venice')
    City.declare('Split')
    City.declare('Brussels')
    City.declare('Copenhagen')
    City = City.create()
    Barcelona, Oslo, Stuttgart, Venice, Split, Brussels, Copenhagen = [ getattr(City, name) for name in ['Barcelona', 'Oslo', 'Stuttgart', 'Venice', 'Split', 'Brussels', 'Copenhagen'] ]
    cities = [Barcelona, Oslo, Stuttgart, Venice, Split, Brussels, Copenhagen]

    # Create variables for the sequence: c0 to c16 (17 variables for 16 days)
    c = [ Const('c_%d' % i, City) for i in range(17) ]

    s = Solver()

    # Constraint: start at Barcelona on day1 (c0)
    s.add(c[0] == Barcelona)

    # Build the allowed flight pairs (including self-loops and both directions of direct flights)
    allowed_pairs = set()
    # Add self-loops (staying in the same city)
    for city in cities:
        allowed_pairs.add((city, city))
    
    # Define the direct flight edges (both directions will be added)
    edges = [
        (Venice, Stuttgart),
        (Oslo, Brussels),
        (Split, Copenhagen),
        (Barcelona, Copenhagen),
        (Barcelona, Venice),
        (Brussels, Venice),
        (Barcelona, Stuttgart),
        (Copenhagen, Brussels),
        (Oslo, Split),
        (Oslo, Venice),
        (Barcelona, Split),
        (Oslo, Copenhagen),
        (Barcelona, Oslo),
        (Copenhagen, Stuttgart),
        (Split, Stuttgart),
        (Copenhagen, Venice),
        (Barcelona, Brussels)
    ]
    for edge in edges:
        allowed_pairs.add(edge)
        allowed_pairs.add((edge[1], edge[0]))
    
    # Add constraints for each consecutive pair (c[i], c[i+1]) must be in allowed_pairs
    for i in range(16):
        constraints_for_i = []
        for (a, b) in allowed_pairs:
            constraints_for_i.append(And(c[i] == a, c[i+1] == b))
        s.add(Or(constraints_for_i))

    # Function to compute total days for a city
    def total_days(city):
        return Sum([If(Or(c[i] == city, c[i+1] == city), 1, 0) for i in range(16)])
    
    # Total days constraints
    s.add(total_days(Barcelona) == 3)
    s.add(total_days(Oslo) == 2)
    s.add(total_days(Stuttgart) == 3)
    s.add(total_days(Venice) == 4)
    s.add(total_days(Split) == 4)
    s.add(total_days(Brussels) == 3)
    s.add(total_days(Copenhagen) == 3)

    # Barcelona must be present on days 1, 2, 3
    # Day1: covered by c0 = Barcelona
    # Day2: must have c1 or c2 is Barcelona
    s.add(Or(c[1] == Barcelona, c[2] == Barcelona))
    # Day3: must have c2 or c3 is Barcelona
    s.add(Or(c[2] == Barcelona, c[3] == Barcelona))

    # Oslo: must be present on day3 or day4
    # Day3: c2 or c3 is Oslo
    # Day4: c3 or c4 is Oslo
    s.add(Or(Or(c[2]==Oslo, c[3]==Oslo), Or(c[3]==Oslo, c[4]==Oslo)))

    # Brussels: must be present on at least one day in [9,11]
    # Day9: c8 or c9 is Brussels
    # Day10: c9 or c10 is Brussels
    # Day11: c10 or c11 is Brussels
    s.add(Or(Or(c[8]==Brussels, c[9]==Brussels), 
             Or(c[9]==Brussels, c[10]==Brussels),
             Or(c[10]==Brussels, c[11]==Brussels)))
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        c_val = [m.evaluate(c[i]) for i in range(17)]
        
        # Map the Z3 constants to string names
        city_names = {
            Barcelona: "Barcelona",
            Oslo: "Oslo",
            Stuttgart: "Stuttgart",
            Venice: "Venice",
            Split: "Split",
            Brussels: "Brussels",
            Copenhagen: "Copenhagen"
        }
        c_val_str = [city_names[val] for val in c_val]
        
        # Build the itinerary
        itinerary = []
        for d in range(16):  # d from 0 to 15, representing day d+1
            day_index = d + 1
            city1 = c_val_str[d]
            city2 = c_val_str[d+1]
            itinerary.append({"day": day_index, "place": city1})
            if city1 != city2:
                itinerary.append({"day": day_index, "place": city2})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()