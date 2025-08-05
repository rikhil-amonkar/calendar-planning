from z3 import *
import json

def main():
    # Define the city enum
    City = Datatype('City')
    City.declare('Vilnius')
    City.declare('Split')
    City.declare('Madrid')
    City.declare('Santorini')
    City = City.create()
    Vilnius, Split, Madrid, Santorini = City.Vilnius, City.Split, City.Madrid, City.Santorini

    # Define the direct flight pairs
    direct_pairs = [
        (Vilnius, Split),
        (Split, Vilnius),
        (Split, Madrid),
        (Madrid, Split),
        (Madrid, Santorini),
        (Santorini, Madrid)
    ]
    
    def is_direct(x, y):
        options = []
        for a, b in direct_pairs:
            options.append(And(x == a, y == b))
        return Or(options)

    # Declare variables
    start_city = Const('start_city', City)
    flight = [Bool('flight_%d' % i) for i in range(14)]
    c = [Const('c_%d' % i, City) for i in range(14)]
    
    s = Solver()
    
    # Constraints for conference days (day 13 and 14)
    s.add(c[12] == Santorini)  # End of day 13
    s.add(c[13] == Santorini)  # End of day 14
    s.add(flight[13] == False)  # No flight on day 14
    
    # Movement constraints for day 1
    s.add(Implies(flight[0], is_direct(start_city, c[0])))
    s.add(Implies(Not(flight[0]), c[0] == start_city))
    
    # Movement constraints for days 2 to 14
    for i in range(1, 14):
        s.add(Implies(flight[i], is_direct(c[i-1], c[i])))
        s.add(Implies(Not(flight[i]), c[i] == c[i-1]))
    
    # Function to count days for a city
    def count_city(X):
        part1 = If(start_city == X, 1, 0)
        part2 = If(And(flight[0], c[0] == X), 1, 0)
        part3 = Sum([If(c[i] == X, 1, 0) for i in range(0, 13)])
        part4 = Sum([If(And(flight[i], c[i] == X), 1, 0) for i in range(1, 14)])
        return part1 + part2 + part3 + part4
    
    # Add constraints for city days
    s.add(count_city(Split) == 5)
    s.add(count_city(Vilnius) == 4)
    s.add(count_city(Madrid) == 6)
    s.add(count_city(Santorini) == 2)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        city_names = {
            Vilnius: "Vilnius",
            Split: "Split",
            Madrid: "Madrid",
            Santorini: "Santorini"
        }
        itinerary_list = []
        for i in range(14):
            c_val = m.evaluate(c[i])
            c_name = city_names[c_val.as_long()]
            itinerary_list.append({"day": i+1, "place": c_name})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()