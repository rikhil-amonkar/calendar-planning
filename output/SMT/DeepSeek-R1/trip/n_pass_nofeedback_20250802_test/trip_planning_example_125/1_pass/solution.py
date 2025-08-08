from z3 import *

def main():
    # Create 15 integer variables for days 1 to 15
    days = [Int('c_%d' % i) for i in range(15)]
    
    s = Solver()
    
    # Each day must be 0 (Stuttgart), 1 (Seville), or 2 (Manchester)
    for d in days:
        s.add(Or(d == 0, d == 1, d == 2))
    
    # Count constraints
    count_stuttgart = Sum([If(d == 0, 1, 0) for d in days])
    count_seville = Sum([If(d == 1, 1, 0) for d in days])
    count_manchester = Sum([If(d == 2, 1, 0) for d in days])
    
    s.add(count_stuttgart == 6)
    s.add(count_seville == 7)
    s.add(count_manchester == 4)
    
    # At least one day in Stuttgart between day1 and day6 (indices 0 to 5)
    s.add(Or([days[i] == 0 for i in range(6)]))
    
    # Flight connectivity constraints for consecutive days
    for i in range(14):  # from day1 to day14 (0-indexed: 0 to 13)
        # Current and next day's city
        c1 = days[i]
        c2 = days[i+1]
        # Allowed transitions: same city, Stuttgart<->Manchester, Manchester<->Seville
        s.add(Or(
            c1 == c2,
            And(c1 == 0, c2 == 2),
            And(c1 == 2, c2 == 0),
            And(c1 == 1, c2 == 2),
            And(c1 == 2, c2 == 1)
        ))
    
    # Check if constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        # Map integers to city names
        city_names = {
            0: 'Stuttgart',
            1: 'Seville',
            2: 'Manchester'
        }
        itinerary = []
        for i in range(15):
            day_index = i
            city_value = model[days[i]].as_long()
            city_name = city_names[city_value]
            itinerary.append({"day": day_index+1, "place": city_name})
        
        # Output as specified
        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No valid itinerary found.")

if __name__ == '__main__':
    main()