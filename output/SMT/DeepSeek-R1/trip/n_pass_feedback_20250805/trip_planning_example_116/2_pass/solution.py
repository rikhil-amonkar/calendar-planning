from z3 import *
import json

def main():
    # Define the variables for the flight days
    a = Int('a')  # Flight day from Split to London
    b = Int('b')  # Flight day from London to Santorini
    
    s = Solver()
    
    # Constraints
    s.add(a >= 1, a <= 18)
    s.add(b >= 1, b <= 18)
    s.add(a < b)  # Flight from Split to London must occur before flight to Santorini
    s.add(a == 6)  # Split stay must be 6 days (days 1 to 6 inclusive)
    s.add(b - a + 1 == 7)  # London stay must be 7 days (days 6 to 12 inclusive)
    s.add(19 - b == 7)  # Santorini stay must be 7 days (days 12 to 18 inclusive)
    
    # Conference constraints: must be in Santorini on days 12 and 18
    # These are satisfied by b=12 and the Santorini segment
    
    if s.check() == sat:
        m = s.model()
        a_val = m[a].as_long()
        b_val = m[b].as_long()
        
        itinerary = []
        for day in range(1, 19):
            if day < a_val:
                places = ["Split"]
            elif day == a_val:
                places = ["Split", "London"]
            elif day < b_val:
                places = ["London"]
            elif day == b_val:
                places = ["London", "Santorini"]
            else:  # day > b_val
                places = ["Santorini"]
            itinerary.append({"day": day, "place": places})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()