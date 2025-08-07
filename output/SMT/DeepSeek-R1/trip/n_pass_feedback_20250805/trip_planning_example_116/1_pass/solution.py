from z3 import *
import json

def main():
    d1 = Int('d1')  # End day of the first stay (Split)
    d2 = Int('d2')  # End day of the second stay (London)

    s = Solver()
    s.add(d1 >= 1, d1 <= 17)
    s.add(d2 >= d1 + 1, d2 <= 18)
    s.add(d1 == 6)  # Split stay must be 6 days
    s.add(d2 - d1 + 1 == 7)  # London stay must be 7 days
    s.add(19 - d2 == 7)  # Santorini stay must be 7 days

    if s.check() == sat:
        m = s.model()
        d1_val = m[d1].as_long()
        d2_val = m[d2].as_long()
        
        itinerary = []
        for day in range(1, 19):
            if day < d1_val:
                places = ["Split"]
            elif day == d1_val:
                places = ["Split", "London"]
            elif day < d2_val:
                places = ["London"]
            elif day == d2_val:
                places = ["London", "Santorini"]
            else:
                places = ["Santorini"]
            itinerary.append({"day": day, "place": places})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()