from z3 import *
import itertools
import json

def main():
    # Travel time matrix (in minutes)
    travel = {
        'Financial District': {
            'Russian Hill': 10,
            'Sunset District': 31,
            'North Beach': 7,
            'The Castro': 23,
            'Golden Gate Park': 23
        },
        'Russian Hill': {
            'Financial District': 11,
            'Sunset District': 23,
            'North Beach': 5,
            'The Castro': 21,
            'Golden Gate Park': 21
        },
        'Sunset District': {
            'Financial District': 30,
            'Russian Hill': 24,
            'North Beach': 29,
            'The Castro': 17,
            'Golden Gate Park': 11
        },
        'North Beach': {
            'Financial District': 8,
            'Russian Hill': 4,
            'Sunset District': 27,
            'The Castro': 22,
            'Golden Gate Park': 22
        },
        'The Castro': {
            'Financial District': 20,
            'Russian Hill': 18,
            'Sunset District': 17,
            'North Beach': 20,
            'Golden Gate Park': 11
        },
        'Golden Gate Park': {
            'Financial District': 26,
            'Russian Hill': 19,
            'Sunset District': 10,
            'North Beach': 24,
            'The Castro': 13
        }
    }
    
    # Availability in minutes since 9:00 AM
    availability = {
        'Patricia': (15, 780),   # 9:15 AM to 10:00 PM
        'Ronald': (285, 495),    # 1:45 PM to 5:15 PM
        'Laura': (210, 225),     # 12:30 PM to 12:45 PM (fixed)
        'Emily': (435, 570),     # 4:15 PM to 6:30 PM
        'Mary': (360, 450)       # 3:00 PM to 4:30 PM
    }
    
    # Minimum meeting durations (in minutes)
    min_duration = {
        'Patricia': 60,
        'Ronald': 105,
        'Laura': 15,
        'Emily': 60,
        'Mary': 60
    }
    
    # Locations for each person
    locations = {
        'Patricia': 'Sunset District',
        'Ronald': 'Russian Hill',
        'Laura': 'North Beach',
        'Emily': 'The Castro',
        'Mary': 'Golden Gate Park'
    }
    
    # Start at Financial District at time 0 (9:00 AM)
    current_location = 'Financial District'
    
    # We must meet Laura at 12:30 PM to 12:45 PM (210 to 225 minutes from 9:00 AM)
    # Morning: Only Patricia is available
    s = Solver()
    
    # Variables for Patricia's meeting
    P_start = Int('P_start')
    P_end = Int('P_end')
    
    # Constraints for Patricia
    s.add(P_start >= availability['Patricia'][0])  # Not before 9:15 AM
    s.add(P_end == P_start + min_duration['Patricia'])
    # Travel from Financial District to Sunset District
    travel_to_p = travel[current_location][locations['Patricia']]
    s.add(P_start >= travel_to_p)  # Arrive at Patricia by P_start
    # After meeting Patricia, travel to Laura at North Beach
    travel_to_l = travel[locations['Patricia']][locations['Laura']]
    s.add(P_end + travel_to_l <= availability['Laura'][0])  # Arrive by 12:30 PM
    
    # Afternoon meetings: Ronald, Emily, Mary (skip one if necessary)
    afternoon_people = ['Ronald', 'Emily', 'Mary']
    best_count = 0
    best_schedule = None
    
    # Try to schedule all three in the afternoon
    for order in itertools.permutations(afternoon_people):
        s2 = s.__copy__()  # Copy the base solver with Patricia and Laura constraints
        times = {}
        for person in afternoon_people:
            times[f'{person}_start'] = Int(f'{person}_start')
            times[f'{person}_end'] = Int(f'{person}_end')
        
        # Start after Laura (12:45 PM = 225 minutes)
        current_time = 225
        current_loc = locations['Laura']
        valid = True
        for i, person in enumerate(order):
            # Travel to the next location
            travel_time = travel[current_loc][locations[person]]
            s2.add(times[f'{person}_start'] >= current_time + travel_time)
            # Meeting duration and availability
            s2.add(times[f'{person}_end'] == times[f'{person}_start'] + min_duration[person])
            s2.add(times[f'{person}_start'] >= availability[person][0])
            s2.add(times[f'{person}_end'] <= availability[person][1])
            # Update current time and location for next travel
            current_time = times[f'{person}_end']
            current_loc = locations[person]
        
        if s2.check() == sat:
            m = s2.model()
            schedule = []
            # Add Patricia
            p_start_val = m[P_start].as_long()
            p_end_val = m[P_end].as_long()
            schedule.append({
                "action": "meet",
                "person": "Patricia",
                "start_time": f"{9 + p_start_val // 60:02d}:{p_start_val % 60:02d}",
                "end_time": f"{9 + p_end_val // 60:02d}:{p_end_val % 60:02d}"
            })
            # Add Laura (fixed)
            schedule.append({
                "action": "meet",
                "person": "Laura",
                "start_time": "12:30",
                "end_time": "12:45"
            })
            # Add afternoon meetings
            for person in order:
                s_val = m[times[f'{person}_start']].as_long()
                e_val = m[times[f'{person}_end']].as_long()
                schedule.append({
                    "action": "meet",
                    "person": person,
                    "start_time": f"{9 + s_val // 60:02d}:{s_val % 60:02d}",
                    "end_time": f"{9 + e_val // 60:02d}:{e_val % 60:02d}"
                })
            best_schedule = schedule
            best_count = len(schedule)
            break
    
    if best_count == 0:  # Could not schedule all three, try subsets of two
        for skip in afternoon_people:
            remaining = [p for p in afternoon_people if p != skip]
            for order in itertools.permutations(remaining):
                s2 = s.__copy__()
                times = {}
                for person in remaining:
                    times[f'{person}_start'] = Int(f'{person}_start')
                    times[f'{person}_end'] = Int(f'{person}_end')
                
                current_time = 225
                current_loc = locations['Laura']
                valid = True
                for i, person in enumerate(order):
                    travel_time = travel[current_loc][locations[person]]
                    s2.add(times[f'{person}_start'] >= current_time + travel_time)
                    s2.add(times[f'{person}_end'] == times[f'{person}_start'] + min_duration[person])
                    s2.add(times[f'{person}_start'] >= availability[person][0])
                    s2.add(times[f'{person}_end'] <= availability[person][1])
                    current_time = times[f'{person}_end']
                    current_loc = locations[person]
                
                if s2.check() == sat:
                    m = s2.model()
                    schedule = []
                    p_start_val = m[P_start].as_long()
                    p_end_val = m[P_end].as_long()
                    schedule.append({
                        "action": "meet",
                        "person": "Patricia",
                        "start_time": f"{9 + p_start_val // 60:02d}:{p_start_val % 60:02d}",
                        "end_time": f"{9 + p_end_val // 60:02d}:{p_end_val % 60:02d}"
                    })
                    schedule.append({
                        "action": "meet",
                        "person": "Laura",
                        "start_time": "12:30",
                        "end_time": "12:45"
                    })
                    for person in order:
                        s_val = m[times[f'{person}_start']].as_long()
                        e_val = m[times[f'{person}_end']].as_long()
                        schedule.append({
                            "action": "meet",
                            "person": person,
                            "start_time": f"{9 + s_val // 60:02d}:{s_val % 60:02d}",
                            "end_time": f"{9 + e_val // 60:02d}:{e_val % 60:02d}"
                        })
                    if len(schedule) > best_count:
                        best_count = len(schedule)
                        best_schedule = schedule
    
    if best_count == 0:  # Only schedule Patricia and Laura
        if s.check() == sat:
            m = s.model()
            best_schedule = []
            p_start_val = m[P_start].as_long()
            p_end_val = m[P_end].as_long()
            best_schedule.append({
                "action": "meet",
                "person": "Patricia",
                "start_time": f"{9 + p_start_val // 60:02d}:{p_start_val % 60:02d}",
                "end_time": f"{9 + p_end_val // 60:02d}:{p_end_val % 60:02d}"
            })
            best_schedule.append({
                "action": "meet",
                "person": "Laura",
                "start_time": "12:30",
                "end_time": "12:45"
            })
        else:  # Only Laura
            best_schedule = [{
                "action": "meet",
                "person": "Laura",
                "start_time": "12:30",
                "end_time": "12:45"
            }]
    
    # Output the solution
    print('SOLUTION:')
    print(json.dumps({"itinerary": best_schedule}))

if __name__ == '__main__':
    main()