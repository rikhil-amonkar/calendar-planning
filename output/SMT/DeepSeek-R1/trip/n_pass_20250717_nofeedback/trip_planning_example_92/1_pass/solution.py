from z3 import Int, Solver, sat
import json

def main():
    t1 = Int('t1')
    t2 = Int('t2')
    s = Solver()
    
    s.add(t1 == 2)
    s.add(t2 >= t1 + 1, t2 <= 12)
    s.add(t2 - t1 + 1 == 5)
    s.add(13 - t2 == 7)
    
    if s.check() != sat:
        print("No solution found")
        return
    
    m = s.model()
    t1_val = m[t1].as_long()
    t2_val = m[t2].as_long()
    
    itinerary = []
    for day in range(1, 13):
        if day < t1_val:
            itinerary.append({"day": day, "place": "Dublin"})
        if day == t1_val:
            itinerary.append({"day": day, "place": "Dublin"})
            itinerary.append({"day": day, "place": "Riga"})
        if day > t1_val and day < t2_val:
            itinerary.append({"day": day, "place": "Riga"})
        if day == t2_val:
            itinerary.append({"day": day, "place": "Riga"})
            itinerary.append({"day": day, "place": "Vilnius"})
        if day > t2_val:
            itinerary.append({"day": day, "place": "Vilnius"})
    
    result = {'itinerary': itinerary}
    print(json.dumps(result))

if __name__ == '__main__':
    main()