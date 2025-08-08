from z3 import *
import json

def main():
    # Define city indices
    Naples = 0
    Seville = 1
    Milan = 2
    city_names = ['Naples', 'Seville', 'Milan']
    
    # Initialize solver
    s = Solver()
    
    # s0: starting city on day1
    s0 = Int('s0')
    s.add(Or(s0 == Naples, s0 == Seville, s0 == Milan))
    
    # c: array of ending cities for each day (0-indexed: day1 to day12)
    c = [Int(f'c_{i}') for i in range(12)]
    for i in range(12):
        s.add(Or(c[i] == Naples, c[i] == Seville, c[i] == Milan))
    
    # Fixed constraints: days 9, 10, 11 (indices 8,9,10) must end in Seville
    s.add(c[8] == Seville)  # day9
    s.add(c[9] == Seville)  # day10
    s.add(c[10] == Seville) # day11
    
    # Flight constraints for day1: from s0 to c[0]
    s.add(Or(
        s0 == c[0],
        And(s0 == Naples, c[0] == Milan),
        And(s0 == Milan, c[0] == Naples),
        And(s0 == Seville, c[0] == Milan),
        And(s0 == Milan, c[0] == Seville)
    ))
    
    # Flight constraints for days 2 to 12: from c[i-1] to c[i]
    for i in range(1, 12):
        s.add(Or(
            c[i-1] == c[i],
            And(c[i-1] == Naples, c[i] == Milan),
            And(c[i-1] == Milan, c[i] == Naples),
            And(c[i-1] == Seville, c[i] == Milan),
            And(c[i-1] == Milan, c[i] == Seville)
        ))
    
    # Total days per city
    total_naples = 0
    total_seville = 0
    total_milan = 0
    
    # Day1: in city if s0==city or c[0]==city
    total_naples += If(Or(s0 == Naples, c[0] == Naples), 1, 0)
    total_seville += If(Or(s0 == Seville, c[0] == Seville), 1, 0)
    total_milan += If(Or(s0 == Milan, c[0] == Milan), 1, 0)
    
    # Days 2 to 12: for day i, in city if c[i-1]==city or c[i]==city
    for i in range(1, 12):  # i from 1 to 11: representing day i+1
        total_naples += If(Or(c[i-1] == Naples, c[i] == Naples), 1, 0)
        total_seville += If(Or(c[i-1] == Seville, c[i] == Seville), 1, 0)
        total_milan += If(Or(c[i-1] == Milan, c[i] == Milan), 1, 0)
    
    # Add constraints for total days
    s.add(total_naples == 3)
    s.add(total_seville == 4)
    s.add(total_milan == 7)
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(12):
            val = m.evaluate(c[i]).as_long()
            itinerary.append(city_names[val])
        
        # Create JSON output
        result = {
            "itinerary": [
                {"day": day, "place": place}
                for day, place in enumerate(itinerary, start=1)
            ]
        }
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()