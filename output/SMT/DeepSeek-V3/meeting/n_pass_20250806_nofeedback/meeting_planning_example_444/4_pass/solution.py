from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the locations and their travel times (in minutes)
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

    # Friends' data
    friends = [
        {
            'name': 'Ronald',
            'location': 'Russian Hill',
            'available_start': (13, 45),  # 1:45 PM
            'available_end': (17, 15),     # 5:15 PM
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
            'available_start': (16, 15),    # 4:15 PM
            'available_end': (18, 30),     # 6:30 PM
            'min_duration': 60
        },
        {
            'name': 'Mary',
            'location': 'Golden Gate Park',
            'available_start': (15, 0),     # 3:00 PM
            'available_end': (16, 30),     # 4:30 PM
            'min_duration': 60
        }
    ]

    # Convert time to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(hour, minute):
        return hour * 60 + minute - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
    def minutes_to_time(m):
        total_minutes = 540 + m
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"

    # Create variables for each friend's meeting start and end times
    meet_vars = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        meet_vars.append((friend, start, end))

    # Constraints for each friend
    for friend, start, end in meet_vars:
        available_start = time_to_minutes(*friend['available_start'])
        available_end = time_to_minutes(*friend['available_end'])
        s.add(start >= available_start)
        s.add(end <= available_end)
        s.add(end - start >= friend['min_duration'])
        s.add(start >= 0)  # Cannot start before 9:00 AM

    # Define the order of meetings
    # We'll try to meet Patricia first, then Laura, Mary, Ronald, and Emily
    order = [
        ('Patricia', 'Sunset District'),
        ('Laura', 'North Beach'),
        ('Mary', 'Golden Gate Park'),
        ('Ronald', 'Russian Hill'),
        ('Emily', 'The Castro')
    ]

    # Get the start and end variables for each in order
    ordered_meetings = []
    for name, loc in order:
        for (friend, start, end) in meet_vars:
            if friend['name'] == name:
                ordered_meetings.append((friend, start, end, loc))
                break

    # Add travel time constraints between consecutive meetings
    for i in range(len(ordered_meetings) - 1):
        current_friend, current_start, current_end, current_loc = ordered_meetings[i]
        next_friend, next_start, next_end, next_loc = ordered_meetings[i + 1]
        current_loc_idx = locations[current_loc]
        next_loc_idx = locations[next_loc]
        travel_time = travel_times[current_loc_idx][next_loc_idx]
        s.add(next_start >= current_end + travel_time)

    # Also, the first meeting must start after arriving at Financial District at 9:00 AM (0 minutes)
    first_friend, first_start, first_end, first_loc = ordered_meetings[0]
    travel_time_first = travel_times[locations['Financial District']][locations[first_loc]]
    s.add(first_start >= travel_time_first)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend, start, end in meet_vars:
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
    else:
        # If no solution found, try a different order
        # Let's try meeting Laura first, then Patricia, Mary, Ronald, Emily
        s.reset()
        meet_vars = []
        for friend in friends:
            start = Int(f"start_{friend['name']}")
            end = Int(f"end_{friend['name']}")
            meet_vars.append((friend, start, end))

        for friend, start, end in meet_vars:
            available_start = time_to_minutes(*friend['available_start'])
            available_end = time_to_minutes(*friend['available_end'])
            s.add(start >= available_start)
            s.add(end <= available_end)
            s.add(end - start >= friend['min_duration'])
            s.add(start >= 0)

        order = [
            ('Laura', 'North Beach'),
            ('Patricia', 'Sunset District'),
            ('Mary', 'Golden Gate Park'),
            ('Ronald', 'Russian Hill'),
            ('Emily', 'The Castro')
        ]

        ordered_meetings = []
        for name, loc in order:
            for (friend, start, end) in meet_vars:
                if friend['name'] == name:
                    ordered_meetings.append((friend, start, end, loc))
                    break

        for i in range(len(ordered_meetings) - 1):
            current_friend, current_start, current_end, current_loc = ordered_meetings[i]
            next_friend, next_start, next_end, next_loc = ordered_meetings[i + 1]
            current_loc_idx = locations[current_loc]
            next_loc_idx = locations[next_loc]
            travel_time = travel_times[current_loc_idx][next_loc_idx]
            s.add(next_start >= current_end + travel_time)

        first_friend, first_start, first_end, first_loc = ordered_meetings[0]
        travel_time_first = travel_times[locations['Financial District']][locations[first_loc]]
        s.add(first_start >= travel_time_first)

        if s.check() == sat:
            model = s.model()
            itinerary = []
            for friend, start, end in meet_vars:
                start_val = model.eval(start).as_long()
                end_val = model.eval(end).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": friend['name'],
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val)
                })
            itinerary.sort(key=lambda x: x['start_time'])
            return {"itinerary": itinerary}
        else:
            # If still no solution, try meeting Patricia, Mary, Ronald, Emily
            s.reset()
            meet_vars = []
            for friend in friends:
                start = Int(f"start_{friend['name']}")
                end = Int(f"end_{friend['name']}")
                meet_vars.append((friend, start, end))

            for friend, start, end in meet_vars:
                available_start = time_to_minutes(*friend['available_start'])
                available_end = time_to_minutes(*friend['available_end'])
                s.add(start >= available_start)
                s.add(end <= available_end)
                s.add(end - start >= friend['min_duration'])
                s.add(start >= 0)

            order = [
                ('Patricia', 'Sunset District'),
                ('Mary', 'Golden Gate Park'),
                ('Ronald', 'Russian Hill'),
                ('Emily', 'The Castro')
            ]

            ordered_meetings = []
            for name, loc in order:
                for (friend, start, end) in meet_vars:
                    if friend['name'] == name:
                        ordered_meetings.append((friend, start, end, loc))
                        break

            for i in range(len(ordered_meetings) - 1):
                current_friend, current_start, current_end, current_loc = ordered_meetings[i]
                next_friend, next_start, next_end, next_loc = ordered_meetings[i + 1]
                current_loc_idx = locations[current_loc]
                next_loc_idx = locations[next_loc]
                travel_time = travel_times[current_loc_idx][next_loc_idx]
                s.add(next_start >= current_end + travel_time)

            first_friend, first_start, first_end, first_loc = ordered_meetings[0]
            travel_time_first = travel_times[locations['Financial District']][locations[first_loc]]
            s.add(first_start >= travel_time_first)

            if s.check() == sat:
                model = s.model()
                itinerary = []
                for friend, start, end in meet_vars:
                    if friend['name'] == 'Laura':
                        continue  # Skip Laura as she's not in this order
                    start_val = model.eval(start).as_long()
                    end_val = model.eval(end).as_long()
                    itinerary.append({
                        "action": "meet",
                        "person": friend['name'],
                        "start_time": minutes_to_time(start_val),
                        "end_time": minutes_to_time(end_val)
                    })
                itinerary.sort(key=lambda x: x['start_time'])
                return {"itinerary": itinerary}
            else:
                return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))