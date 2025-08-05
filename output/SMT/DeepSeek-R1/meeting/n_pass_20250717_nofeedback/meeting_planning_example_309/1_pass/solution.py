from z3 import *

def min_to_time(minutes):
    total_minutes = minutes
    h = 9 + total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Define the meeting indices: 0=Nancy, 1=Mary, 2=Jessica
    first, second, third = Ints('first second third')
    s0, s1, s2 = Ints('s0 s1 s2')  # start times for the first, second, third meeting in the schedule

    # Travel times from FD (starting point) to each meeting location
    travel_first = If(first == 0, 5, If(first == 1, 17, 19))

    # Travel times between meeting locations (3x3 matrix for meeting indices)
    def travel_between_z3(i, j):
        return If(And(i == 0, j == 1), 17,
              If(And(i == 0, j == 2), 22,
              If(And(i == 1, j == 0), 16,
              If(And(i == 1, j == 2), 16,
              If(And(i == 2, j == 0), 18,
              If(And(i == 2, j == 1), 16, 0))))))
    
    travel_second = travel_between_z3(first, second)
    travel_third = travel_between_z3(second, third)

    # Durations for each meeting
    dur_first = If(first == 0, 90, If(first == 1, 75, 45))
    dur_second = If(second == 0, 90, If(second == 1, 75, 45))
    dur_third = If(third == 0, 90, If(third == 1, 75, 45))

    s_Nancy = If(first == 0, s0, If(second == 0, s1, s2))
    s_Mary = If(first == 1, s0, If(second == 1, s1, s2))
    s_Jessica = If(first == 2, s0, If(second == 2, s1, s2))

    s = Solver()

    # Constraints for the order and range
    s.add(Distinct(first, second, third))
    s.add(first >= 0, first <= 2)
    s.add(second >= 0, second <= 2)
    s.add(third >= 0, third <= 2)

    # Constraints for start times considering travel
    s.add(s0 >= travel_first)
    s.add(s1 >= s0 + dur_first + travel_second)
    s.add(s2 >= s1 + dur_second + travel_third)

    # Time window constraints
    s.add(s_Nancy >= 30, s_Nancy + 90 <= 270)     # Nancy: 9:30 AM to 1:30 PM, min 90 mins
    s.add(s_Mary >= 0, s_Mary + 75 <= 720)         # Mary: 7:00 AM to 9:00 PM, min 75 mins
    s.add(s_Jessica >= 135, s_Jessica + 45 <= 285) # Jessica: 11:15 AM to 1:45 PM, min 45 mins

    if s.check() == sat:
        m = s.model()
        nancy_start = m.evaluate(s_Nancy).as_long()
        mary_start = m.evaluate(s_Mary).as_long()
        jessica_start = m.evaluate(s_Jessica).as_long()
        
        nancy_end = nancy_start + 90
        mary_end = mary_start + 75
        jessica_end = jessica_start + 45
        
        itinerary = [
            {"action": "meet", "person": "Nancy", "start_time": min_to_time(nancy_start), "end_time": min_to_time(nancy_end)},
            {"action": "meet", "person": "Mary", "start_time": min_to_time(mary_start), "end_time": min_to_time(mary_end)},
            {"action": "meet", "person": "Jessica", "start_time": min_to_time(jessica_start), "end_time": min_to_time(jessica_end)}
        ]
        
        # Format the output as required
        import json
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("No feasible schedule found")

if __name__ == "__main__":
    main()