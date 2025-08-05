import z3
import json

def main():
    days = 18
    c = [z3.Int('c_%d' % i) for i in range(1, days+1)]
    solver = z3.Solver()
    
    # Define city constants
    Split = 0
    Santorini = 1
    London = 2
    
    # Conference constraints: day 12 and 18 must be Santorini
    solver.add(c[11] == Santorini)   # day12 (index 11)
    solver.add(c[17] == Santorini)   # day18 (index 17)
    
    # Fixed days for Split (days 1-5) and London (days 7-11) and Santorini (days 13-18)
    for i in range(0, 5):   # days 1-5 (indices 0-4)
        solver.add(c[i] == Split)
    for i in range(6, 11):  # days 7-11 (indices 6-10)
        solver.add(c[i] == London)
    for i in range(12, 18): # days 13-18 (indices 12-17)
        solver.add(c[i] == Santorini)
    
    # Day 6 (index 5) can be either Split or London
    solver.add(z3.Or(c[5] == Split, c[5] == London))
    
    if solver.check() == z3.sat:
        model = solver.model()
        itinerary = []
        city_names = {Split: "Split", Santorini: "Santorini", London: "London"}
        for i in range(days):
            day = i + 1
            city_val = model[c[i]].as_long()
            place = city_names.get(city_val, "Unknown")
            itinerary.append({"day": day, "place": place})
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()