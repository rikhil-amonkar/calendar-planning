from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    sarah_start = Int('sarah_start')
    sarah_end = Int('sarah_end')
    richard_start = Int('richard_start')
    richard_end = Int('richard_end')
    elizabeth_start = Int('elizabeth_start')
    elizabeth_end = Int('elizabeth_end')
    michelle_start = Int('michelle_start')
    michelle_end = Int('michelle_end')

    # Convert friend availability windows to minutes since 9:00 AM
    sarah_available_start = 105  # 10:45 AM
    sarah_available_end = 600    # 7:00 PM
    richard_available_start = 165  # 11:45 AM
    richard_available_end = 405    # 3:45 PM
    elizabeth_available_start = 120  # 11:00 AM
    elizabeth_available_end = 495    # 5:15 PM
    michelle_available_start = 435  # 6:15 PM
    michelle_available_end = 585    # 8:45 PM

    # Minimum meeting durations
    sarah_min_duration = 30
    richard_min_duration = 90
    elizabeth_min_duration = 120
    michelle_min_duration = 90

    # Meeting duration constraints
    s.add(sarah_end - sarah_start >= sarah_min_duration)
    s.add(richard_end - richard_start >= richard_min_duration)
    s.add(elizabeth_end - elizabeth_start >= elizabeth_min_duration)
    s.add(michelle_end - michelle_start >= michelle_min_duration)

    # Availability constraints
    s.add(sarah_start >= sarah_available_start, sarah_end <= sarah_available_end)
    s.add(richard_start >= richard_available_start, richard_end <= richard_available_end)
    s.add(elizabeth_start >= elizabeth_available_start, elizabeth_end <= elizabeth_available_end)
    s.add(michelle_start >= michelle_available_start, michelle_end <= michelle_available_end)

    # Travel times between locations
    travel = {
        ('Richmond', 'Sunset'): 11,
        ('Richmond', 'Haight'): 10,
        ('Richmond', 'Mission'): 20,
        ('Richmond', 'Park'): 9,
        ('Sunset', 'Richmond'): 12,
        ('Sunset', 'Haight'): 15,
        ('Sunset', 'Mission'): 24,
        ('Sunset', 'Park'): 11,
        ('Haight', 'Richmond'): 10,
        ('Haight', 'Sunset'): 15,
        ('Haight', 'Mission'): 11,
        ('Haight', 'Park'): 7,
        ('Mission', 'Richmond'): 20,
        ('Mission', 'Sunset'): 24,
        ('Mission', 'Haight'): 12,
        ('Mission', 'Park'): 17,
        ('Park', 'Richmond'): 7,
        ('Park', 'Sunset'): 10,
        ('Park', 'Haight'): 7,
        ('Park', 'Mission'): 17,
    }

    # Decision variables for meeting order
    meet_first = Int('meet_first')
    meet_second = Int('meet_second')
    meet_third = Int('meet_third')
    meet_fourth = Int('meet_fourth')

    # Define possible meeting orders (1: Elizabeth, 2: Richard, 3: Sarah, 4: Michelle)
    s.add(Distinct(meet_first, meet_second, meet_third, meet_fourth))
    s.add(And(meet_first >= 1, meet_first <= 4))
    s.add(And(meet_second >= 1, meet_second <= 4))
    s.add(And(meet_third >= 1, meet_third <= 4))
    s.add(And(meet_fourth >= 1, meet_fourth <= 4))

    # Starting location is Richmond District
    current_location = 'Richmond'
    current_time = 0  # 9:00 AM

    # Create variables to track locations and times
    loc1 = String('loc1')
    time1 = Int('time1')
    loc2 = String('loc2')
    time2 = Int('time2')
    loc3 = String('loc3')
    time3 = Int('time3')
    loc4 = String('loc4')
    time4 = Int('time4')

    # Constraints for first meeting
    s.add(If(meet_first == 1, 
             And(elizabeth_start >= current_time + travel[(current_location, 'Mission')],
                 time1 == elizabeth_end,
                 loc1 == 'Mission'),
          If(meet_first == 2,
             And(richard_start >= current_time + travel[(current_location, 'Haight')],
                 time1 == richard_end,
                 loc1 == 'Haight'),
          If(meet_first == 3,
             And(sarah_start >= current_time + travel[(current_location, 'Sunset')],
                 time1 == sarah_end,
                 loc1 == 'Sunset'),
             And(michelle_start >= current_time + travel[(current_location, 'Park')],
                 time1 == michelle_end,
                 loc1 == 'Park')))))

    # Constraints for second meeting
    s.add(If(meet_second == 1, 
             And(elizabeth_start >= time1 + travel[(loc1, 'Mission')],
                 time2 == elizabeth_end,
                 loc2 == 'Mission'),
          If(meet_second == 2,
             And(richard_start >= time1 + travel[(loc1, 'Haight')],
                 time2 == richard_end,
                 loc2 == 'Haight'),
          If(meet_second == 3,
             And(sarah_start >= time1 + travel[(loc1, 'Sunset')],
                 time2 == sarah_end,
                 loc2 == 'Sunset'),
             And(michelle_start >= time1 + travel[(loc1, 'Park')],
                 time2 == michelle_end,
                 loc2 == 'Park')))))

    # Constraints for third meeting
    s.add(If(meet_third == 1, 
             And(elizabeth_start >= time2 + travel[(loc2, 'Mission')],
                 time3 == elizabeth_end,
                 loc3 == 'Mission'),
          If(meet_third == 2,
             And(richard_start >= time2 + travel[(loc2, 'Haight')],
                 time3 == richard_end,
                 loc3 == 'Haight'),
          If(meet_third == 3,
             And(sarah_start >= time2 + travel[(loc2, 'Sunset')],
                 time3 == sarah_end,
                 loc3 == 'Sunset'),
             And(michelle_start >= time2 + travel[(loc2, 'Park')],
                 time3 == michelle_end,
                 loc3 == 'Park')))))

    # Constraints for fourth meeting
    s.add(If(meet_fourth == 1, 
             And(elizabeth_start >= time3 + travel[(loc3, 'Mission')],
                 time4 == elizabeth_end,
                 loc4 == 'Mission'),
          If(meet_fourth == 2,
             And(richard_start >= time3 + travel[(loc3, 'Haight')],
                 time4 == richard_end,
                 loc4 == 'Haight'),
          If(meet_fourth == 3,
             And(sarah_start >= time3 + travel[(loc3, 'Sunset')],
                 time4 == sarah_end,
                 loc4 == 'Sunset'),
             And(michelle_start >= time3 + travel[(loc3, 'Park')],
                 time4 == michelle_end,
                 loc4 == 'Park')))))

    # Ensure all meetings are scheduled
    s.add(Or(meet_first == 1, meet_second == 1, meet_third == 1, meet_fourth == 1))
    s.add(Or(meet_first == 2, meet_second == 2, meet_third == 2, meet_fourth == 2))
    s.add(Or(meet_first == 3, meet_second == 3, meet_third == 3, meet_fourth == 3))
    s.add(Or(meet_first == 4, meet_second == 4, meet_third == 4, meet_fourth == 4))

    # Try to minimize total time
    s.minimize(time4)

    if s.check() == sat:
        model = s.model()
        def get_meeting_time(var):
            return model[var].as_long() if model[var] is not None else 0
        
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{9 + hours:02d}:{mins:02d}"

        itinerary = []
        order = [
            (model[meet_first].as_long(), 'first'),
            (model[meet_second].as_long(), 'second'),
            (model[meet_third].as_long(), 'third'),
            (model[meet_fourth].as_long(), 'fourth')
        ]

        for meeting_num, pos in order:
            if meeting_num == 1:
                start = get_meeting_time(elizabeth_start)
                end = get_meeting_time(elizabeth_end)
                person = 'Elizabeth'
            elif meeting_num == 2:
                start = get_meeting_time(richard_start)
                end = get_meeting_time(richard_end)
                person = 'Richard'
            elif meeting_num == 3:
                start = get_meeting_time(sarah_start)
                end = get_meeting_time(sarah_end)
                person = 'Sarah'
            else:
                start = get_meeting_time(michelle_start)
                end = get_meeting_time(michelle_end)
                person = 'Michelle'
            
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling()
print(solution)