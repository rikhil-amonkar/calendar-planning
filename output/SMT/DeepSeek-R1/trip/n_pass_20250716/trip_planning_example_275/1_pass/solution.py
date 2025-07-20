from z3 import Solver, Int, sat

def main():
    s = Solver()
    X = Int('X')
    Y = Int('Y')
    Z = Int('Z')
    
    s.add(X >= 1, X <= 14)
    s.add(Y >= X, Y <= 14)
    s.add(Z >= Y, Z <= 14)
    
    s.add(Y - X + 1 == 5)
    s.add(Z - Y + 1 == 6)
    s.add(14 - Z + 1 == 2)
    
    if s.check() == sat:
        m = s.model()
        X_val = m[X].as_long()
        Y_val = m[Y].as_long()
        Z_val = m[Z].as_long()
        
        itinerary = [
            {"day_range": "Day 1-{}".format(X_val), "place": "Vilnius"},
            {"day_range": "Day {}".format(X_val), "place": "Vilnius"},
            {"day_range": "Day {}".format(X_val), "place": "Split"},
            {"day_range": "Day {}-{}".format(X_val, Y_val), "place": "Split"},
            {"day_range": "Day {}".format(Y_val), "place": "Split"},
            {"day_range": "Day {}".format(Y_val), "place": "Madrid"},
            {"day_range": "Day {}-{}".format(Y_val, Z_val), "place": "Madrid"},
            {"day_range": "Day {}".format(Z_val), "place": "Madrid"},
            {"day_range": "Day {}".format(Z_val), "place": "Santorini"},
            {"day_range": "Day {}-14".format(Z_val), "place": "Santorini"}
        ]
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()