import z3
import json

def main():
    # Convert all times to minutes from midnight for easier arithmetic
    start_day = 9 * 60  # 9:00 AM
    daniel_available_start = 19 * 60  # 7:00 PM
    daniel_available_end = 20 * 60 + 15  # 8:15 PM

    travel_RH_to_RD = 14  # minutes

    # Define the time we leave Russian Hill as a Z3 integer variable
    T_leave_RH = z3.Int('T_leave_RH')
    solver = z3.Solver()
    
    # Constraints: 
    # 1. We cannot leave Russian Hill before 9:00 AM.
    # 2. We must leave early enough to arrive at Richmond District by 7:00 PM.
    solver.add(T_leave_RH >= start_day)
    solver.add(T_leave_RH + travel_RH_to_RD <= daniel_available_start)
    
    # Check if the constraints are satisfiable
    if solver.check() == z3.sat:
        # The meeting with Daniel is fixed from 7:00 PM to 8:15 PM
        itinerary = [{
            "action": "meet",
            "person": "Daniel",
            "start_time": "19:00",
            "end_time": "20:15"
        }]
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # If no solution found, output empty itinerary
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()