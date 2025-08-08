import json
from z3 import Solver, Int, Or, And, Implies, If, sat
import os
import sys

def write_output(data):
    try:
        os.write(1, data)
    except:
        try:
            os.write(2, data)
        except:
            pass

def main():
    try:
        cities = ["Dublin", "Helsinki", "Riga", "Reykjavik", "Vienna", "Tallinn"]
        required_days = [5, 3, 3, 2, 2, 5]
        
        allowed_flights = [
            (0, 1), (1, 0),
            (0, 2), (2, 0),
            (0, 3), (3, 0),
            (0, 4), (4, 0),
            (0, 5), (5, 0),
            (1, 2), (2, 1),
            (1, 3), (3, 1),
            (1, 4), (4, 1),
            (1, 5), (5, 1),
            (2, 4), (4, 2),
            (3, 4), (4, 3),
            (2, 5)
        ]
        
        s = Solver()
        L = [Int(f'L_{i}') for i in range(16)]
        
        for i in range(16):
            s.add(L[i] >= 0, L[i] <= 5)
        
        for t in range(1, 16):
            current_from = L[t-1]
            current_to = L[t]
            flight_options = []
            for flight in allowed_flights:
                a, b = flight
                flight_options.append(And(current_from == a, current_to == b))
            s.add(Implies(current_from != current_to, Or(flight_options)))
        
        for c_idx in range(6):
            total_days = 0
            for day in range(1, 16):
                total_days += If(Or(L[day-1] == c_idx, L[day] == c_idx), 1, 0)
            s.add(total_days == required_days[c_idx])
        
        s.add(Or(
            Or(L[2] == 1, L[3] == 1),
            Or(L[3] == 1, L[4] == 1),
            Or(L[4] == 1, L[5] == 1)
        ))
        
        s.add(Or(
            Or(L[1] == 4, L[2] == 4),
            Or(L[2] == 4, L[3] == 4)
        ))
        
        tallinn_days = []
        for day in range(7, 12):
            tallinn_days.append(Or(L[day-1] == 5, L[day] == 5))
        s.add(Or(tallinn_days))
        
        if s.check() == sat:
            model = s.model()
            itinerary = []
            for day in range(1, 16):
                start_city = model[L[day-1]].as_long()
                end_city = model[L[day]].as_long()
                if start_city == end_city:
                    cities_list = [cities[start_city]]
                else:
                    cities_list = [cities[start_city], cities[end_city]]
                itinerary.append({"day": day, "cities": cities_list})
            result = json.dumps({"itinerary": itinerary})
            write_output(result.encode('utf-8'))
        else:
            result = json.dumps({"error": "No solution found"})
            write_output(result.encode('utf-8'))
    except Exception as e:
        error_msg = json.dumps({"error": f"Unexpected error: {str(e)}"})
        write_output(error_msg.encode('utf-8'))

if __name__ == "__main__":
    main()