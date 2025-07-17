from z3 import *
import json

def solve_scheduling_problem():
    # Create solver instance
    s = Solver()

    # Variables for meeting Stephanie
    steph_start = Int('steph_start')
    steph_end = Int('steph_end')

    # Variables for meeting John
    john_start = Int('john_start')
    john_end = Int('john_end')

    # Convert all times to minutes since midnight
    arrival_time = 9 * 60  # 9:00 AM
    steph_avail_start = 8 * 60 + 15  # 8:15 AM
    steph_avail_end = 11 * 60 + 30  # 11:30 AM
    john_avail_start = 10 * 60 + 15  # 10:15 AM
    john_avail_end = 20 * 60 + 45  # 8:45 PM

    # Travel times in minutes
    emb_to_fin = 5  # Embarcadero to Financial District
    fin_to_alamo = 17  # Financial District to Alamo Square

    # Constraints for meeting Stephanie
    s.add(steph_start >= max(arrival_time, steph_avail_start))
    s.add(steph_end <= steph_avail_end)
    s.add(steph_end - steph_start >= 90)  # At least 90 minutes

    # Constraints for meeting John
    s.add(john_start >= john_avail_start)
    s.add(john_end <= john_avail_end)
    s.add(john_end - john_start >= 30)  # At least 30 minutes

    # Travel time constraint
    s.add(john_start >= steph_end + fin_to_alamo)

    # Additional constraint to ensure meetings don't overlap with travel
    s.add(john_start > steph_end)

    # Optimize to find earliest possible meetings
    s.minimize(john_end)

    if s.check() == sat:
        model = s.model()
        steph_s = model.eval(steph_start).as_long()
        steph_e = model.eval(steph_end).as_long()
        john_s = model.eval(john_start).as_long()
        john_e = model.eval(john_end).as_long()

        def to_time(minutes):
            return f"{minutes//60:02d}:{minutes%60:02d}"

        itinerary = [
            {"action": "meet", "person": "Stephanie", 
             "start_time": to_time(steph_s), "end_time": to_time(steph_e)},
            {"action": "meet", "person": "John", 
             "start_time": to_time(john_s), "end_time": to_time(john_e)}
        ]

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

result = solve_scheduling_problem()
print(json.dumps(result, indent=2))