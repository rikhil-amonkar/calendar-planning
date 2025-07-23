from z3 import *
import json

def solve_scheduling():
    s = Solver()

    # Convert times to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Define time variables
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')
    william_start = Int('william_start')
    william_end = Int('william_end')

    # Meeting durations
    emily_duration = 105
    barbara_duration = 60
    william_duration = 105

    # Availability windows
    emily_window = (time_to_minutes("11:45"), time_to_minutes("15:15"))
    barbara_window = (time_to_minutes("16:45"), time_to_minutes("18:15"))
    william_window = (time_to_minutes("17:15"), time_to_minutes("19:00"))

    # Travel times between locations (in minutes)
    travel_times = {
        ('Castro', 'Alamo Square'): 8,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'Chinatown'): 16,
        ('Union Square', 'Chinatown'): 7,
        ('Chinatown', 'Union Square'): 7
    }

    # Meeting constraints
    s.add(emily_start >= emily_window[0])
    s.add(emily_end <= emily_window[1])
    s.add(emily_end == emily_start + emily_duration)

    s.add(barbara_start >= barbara_window[0])
    s.add(barbara_end <= barbara_window[1])
    s.add(barbara_end == barbara_start + barbara_duration)

    s.add(william_start >= william_window[0])
    s.add(william_end <= william_window[1])
    s.add(william_end == william_start + william_duration)

    # Starting at Castro at 9:00 AM (540 minutes)
    s.add(emily_start >= 540 + travel_times[('Castro', 'Alamo Square')])

    # Define possible meeting orders
    # Order 1: Emily → Barbara → William
    order1 = And(
        barbara_start >= emily_end + travel_times[('Alamo Square', 'Union Square')],
        william_start >= barbara_end + travel_times[('Union Square', 'Chinatown')]
    )

    # Order 2: Emily → William → Barbara
    order2 = And(
        william_start >= emily_end + travel_times[('Alamo Square', 'Chinatown')],
        barbara_start >= william_end + travel_times[('Chinatown', 'Union Square')]
    )

    # Try both possible orders
    s.add(Or(order1, order2))

    if s.check() == sat:
        model = s.model()
        itinerary = []

        # Determine which order was chosen
        if is_true(model.eval(order1)):
            # Emily → Barbara → William
            emily_s = model[emily_start].as_long()
            emily_e = model[emily_end].as_long()
            barbara_s = model[barbara_start].as_long()
            barbara_e = model[barbara_end].as_long()
            william_s = model[william_start].as_long()
            william_e = model[william_end].as_long()
            
            itinerary = [
                {"action": "meet", "person": "Emily", "start_time": minutes_to_time(emily_s), "end_time": minutes_to_time(emily_e)},
                {"action": "meet", "person": "Barbara", "start_time": minutes_to_time(barbara_s), "end_time": minutes_to_time(barbara_e)},
                {"action": "meet", "person": "William", "start_time": minutes_to_time(william_s), "end_time": minutes_to_time(william_e)}
            ]
        else:
            # Emily → William → Barbara
            emily_s = model[emily_start].as_long()
            emily_e = model[emily_end].as_long()
            william_s = model[william_start].as_long()
            william_e = model[william_end].as_long()
            barbara_s = model[barbara_start].as_long()
            barbara_e = model[barbara_end].as_long()
            
            itinerary = [
                {"action": "meet", "person": "Emily", "start_time": minutes_to_time(emily_s), "end_time": minutes_to_time(emily_e)},
                {"action": "meet", "person": "William", "start_time": minutes_to_time(william_s), "end_time": minutes_to_time(william_e)},
                {"action": "meet", "person": "Barbara", "start_time": minutes_to_time(barbara_s), "end_time": minutes_to_time(barbara_e)}
            ]

        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found."}

result = solve_scheduling()
print(json.dumps(result, indent=2))