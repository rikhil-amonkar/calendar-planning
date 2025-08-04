from z3 import *
import json

def solve_scheduling_problem():
    s = Solver()

    # Define variables in minutes since 9:00AM
    sarah_start = Int('sarah_start')
    sarah_end = Int('sarah_end')
    jeffrey_start = Int('jeffrey_start')
    jeffrey_end = Int('jeffrey_end')
    brian_start = Int('brian_start')
    brian_end = Int('brian_end')

    # Convert availability windows to minutes
    sarah_window_start = 16*60 - 9*60  # 4:00PM = 420 minutes
    sarah_window_end = 18*60 + 15 - 9*60  # 6:15PM = 555 minutes
    jeffrey_window_start = 15*60 - 9*60  # 3:00PM = 360 minutes
    jeffrey_window_end = 22*60 - 9*60  # 10:00PM = 780 minutes
    brian_window_start = 16*60 - 9*60  # 4:00PM = 420 minutes
    brian_window_end = 17*60 + 30 - 9*60  # 5:30PM = 510 minutes

    # Meeting durations
    sarah_duration = 60
    jeffrey_duration = 75
    brian_duration = 75

    # Basic constraints
    s.add(sarah_start >= sarah_window_start, sarah_end <= sarah_window_end)
    s.add(sarah_end == sarah_start + sarah_duration)
    s.add(jeffrey_start >= jeffrey_window_start, jeffrey_end <= jeffrey_window_end)
    s.add(jeffrey_end == jeffrey_start + jeffrey_duration)
    s.add(brian_start >= brian_window_start, brian_end <= brian_window_end)
    s.add(brian_end == brian_start + brian_duration)

    # Travel times (minutes)
    travel = {
        ('Sunset District', 'North Beach'): 29,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Alamo Square'): 17,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Alamo Square'): 16,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Alamo Square'): 15,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Union Square'): 14,
    }

    # Try different meeting orders
    orders = [
        ['Jeffrey', 'Sarah', 'Brian'],
        ['Jeffrey', 'Brian', 'Sarah'],
        ['Sarah', 'Jeffrey', 'Brian'],
        ['Sarah', 'Brian', 'Jeffrey'],
        ['Brian', 'Jeffrey', 'Sarah'],
        ['Brian', 'Sarah', 'Jeffrey']
    ]

    for order in orders:
        temp_s = Solver()
        temp_s.add(s.assertions())
        
        current_loc = 'Sunset District'
        current_time = 0
        
        for name in order:
            if name == 'Sarah':
                loc = 'North Beach'
                start = sarah_start
                end = sarah_end
            elif name == 'Jeffrey':
                loc = 'Union Square'
                start = jeffrey_start
                end = jeffrey_end
            else:  # Brian
                loc = 'Alamo Square'
                start = brian_start
                end = brian_end
            
            # Get travel time
            tt = travel.get((current_loc, loc)) or travel.get((loc, current_loc))
            if not tt:
                break
            
            # Arrival time
            arrival = current_time + tt
            temp_s.add(start >= arrival)
            
            current_time = end
            current_loc = loc
        
        if temp_s.check() == sat:
            m = temp_s.model()
            
            def to_time(minutes):
                h = 9 + minutes // 60
                m = minutes % 60
                return f"{h:02d}:{m:02d}"
            
            itinerary = []
            for name in ['Jeffrey', 'Sarah', 'Brian']:
                if name == 'Jeffrey':
                    s_start = m.eval(jeffrey_start).as_long()
                    s_end = m.eval(jeffrey_end).as_long()
                elif name == 'Sarah':
                    s_start = m.eval(sarah_start).as_long()
                    s_end = m.eval(sarah_end).as_long()
                else:
                    s_start = m.eval(brian_start).as_long()
                    s_end = m.eval(brian_end).as_long()
                
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": to_time(s_start),
                    "end_time": to_time(s_end)
                })
            
            # Sort by start time
            itinerary.sort(key=lambda x: x['start_time'])
            return {"itinerary": itinerary}

    return {"itinerary": []}

result = solve_scheduling_problem()
print(json.dumps(result, indent=2))