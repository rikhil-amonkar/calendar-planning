from z3 import *
import json

def solve_scheduling_problem():
    s = Solver()

    # Locations and travel times (in minutes)
    locations = {
        'Financial District': 0,
        'Russian Hill': 1,
        'Sunset District': 2,
        'North Beach': 3,
        'The Castro': 4,
        'Golden Gate Park': 5
    }

    travel_times = [
        [0, 10, 31, 7, 23, 23],  # Financial District to others
        [11, 0, 23, 5, 21, 21],    # Russian Hill to others
        [30, 24, 0, 29, 17, 11],   # Sunset District to others
        [8, 4, 27, 0, 22, 22],     # North Beach to others
        [20, 18, 17, 20, 0, 11],   # The Castro to others
        [26, 19, 10, 24, 13, 0]    # Golden Gate Park to others
    ]

    friends = [
        {
            'name': 'Ronald',
            'location': 'Russian Hill',
            'available_start': (13, 45),  # 1:45 PM
            'available_end': (17, 15),    # 5:15 PM
            'min_duration': 105
        },
        {
            'name': 'Patricia',
            'location': 'Sunset District',
            'available_start': (9, 15),
            'available_end': (22, 0),
            'min_duration': 60
        },
        {
            'name': 'Laura',
            'location': 'North Beach',
            'available_start': (12, 30),
            'available_end': (12, 45),
            'min_duration': 15
        },
        {
            'name': 'Emily',
            'location': 'The Castro',
            'available_start': (16, 15),  # 4:15 PM
            'available_end': (18, 30),    # 6:30 PM
            'min_duration': 60
        },
        {
            'name': 'Mary',
            'location': 'Golden Gate Park',
            'available_start': (15, 0),   # 3:00 PM
            'available_end': (16, 30),    # 4:30 PM
            'min_duration': 60
        }
    ]

    def time_to_minutes(hour, minute):
        return hour * 60 + minute - 540  # 9:00 AM is 540 minutes

    def minutes_to_time(m):
        total_minutes = 540 + m
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"

    # Create variables for each friend's meeting
    meet_vars = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        meet = Bool(f"meet_{friend['name']}")  # Whether to meet this friend
        meet_vars.append((friend, start, end, meet))

    # Constraints for each friend
    for friend, start, end, meet in meet_vars:
        available_start = time_to_minutes(*friend['available_start'])
        available_end = time_to_minutes(*friend['available_end'])
        s.add(Implies(meet, start >= available_start))
        s.add(Implies(meet, end <= available_end))
        s.add(Implies(meet, end - start >= friend['min_duration']))
        s.add(Implies(meet, start >= 0))

    # Try different meeting orders
    possible_orders = [
        ['Patricia', 'Laura', 'Mary', 'Ronald', 'Emily'],
        ['Patricia', 'Mary', 'Ronald', 'Emily'],
        ['Laura', 'Patricia', 'Mary', 'Ronald', 'Emily'],
        ['Patricia', 'Mary', 'Emily', 'Ronald'],
        ['Mary', 'Ronald', 'Emily']
    ]

    for order in possible_orders:
        s.push()  # Create a backtracking point
        
        # Force the meeting order
        for i in range(len(order) - 1):
            current_name = order[i]
            next_name = order[i + 1]
            
            # Find the corresponding variables
            current_vars = None
            next_vars = None
            for friend, start, end, meet in meet_vars:
                if friend['name'] == current_name:
                    current_vars = (friend, start, end, meet)
                if friend['name'] == next_name:
                    next_vars = (friend, start, end, meet)
            
            if current_vars and next_vars:
                current_friend, current_start, current_end, current_meet = current_vars
                next_friend, next_start, next_end, next_meet = next_vars
                
                # Add travel time constraint
                current_loc = locations[current_friend['location']]
                next_loc = locations[next_friend['location']]
                travel_time = travel_times[current_loc][next_loc]
                s.add(Implies(And(current_meet, next_meet), 
                      next_start >= current_end + travel_time)

        # First meeting must start after arriving at Financial District
        first_name = order[0]
        for friend, start, end, meet in meet_vars:
            if friend['name'] == first_name:
                first_loc = locations[friend['location']]
                travel_time = travel_times[locations['Financial District']][first_loc]
                s.add(Implies(meet, start >= travel_time))
                break

        # Maximize number of meetings
        num_meetings = Int('num_meetings')
        s.add(num_meetings == Sum([If(meet, 1, 0) for _, _, _, meet in meet_vars]))
        s.maximize(num_meetings)

        if s.check() == sat:
            model = s.model()
            itinerary = []
            for friend, start, end, meet in meet_vars:
                if is_true(model.eval(meet)):
                    start_val = model.eval(start).as_long()
                    end_val = model.eval(end).as_long()
                    itinerary.append({
                        "action": "meet",
                        "person": friend['name'],
                        "start_time": minutes_to_time(start_val),
                        "end_time": minutes_to_time(end_val)
                    })
            # Sort itinerary by start time
            itinerary.sort(key=lambda x: x['start_time'])
            return {"itinerary": itinerary}
        
        s.pop()  # Backtrack

    return {"itinerary": []}

result = solve_scheduling_problem()
print(json.dumps(result, indent=2))