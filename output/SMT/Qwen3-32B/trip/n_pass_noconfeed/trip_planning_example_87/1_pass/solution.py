import z3
import json

def main():
    solver = z3.Solver()
    
    # Define transition days between cities
    T1 = z3.Int('T1')  # Transition from Riga to Amsterdam
    T2 = z3.Int('T2')  # Transition from Amsterdam to Mykonos
    
    # Constraints for required durations in each city
    solver.add(T1 == 2)  # Riga duration: 2 days (Day 1-2)
    solver.add(T2 - T1 + 1 == 2)  # Amsterdam duration: 2 days (Day 2-3)
    solver.add(7 - T2 + 1 == 5)  # Mykonos duration: 5 days (Day 3-7)
    
    # Check transitions are allowed between cities
    # Riga -> Amsterdam and Amsterdam -> Mykonos are valid direct flights
    # No additional constraints needed for flight connectivity
    
    if solver.check() == z3.sat:
        model = solver.model()
        t1 = model[T1].as_long()
        t2 = model[T2].as_long()
        
        itinerary = [
            {"day_range": f"Day 1-{t1}", "place": "Riga"},
            {"day_range": f"Day {t1}-{t2}", "place": "Amsterdam"},
            {"day_range": f"Day {t2}-7", "place": "Mykonos"}
        ]
        
        # Output result as JSON
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()