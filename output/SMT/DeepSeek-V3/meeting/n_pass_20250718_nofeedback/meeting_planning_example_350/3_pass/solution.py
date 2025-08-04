from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    # Mary at Pacific Heights: 10:00 AM to 7:00 PM (min 45 minutes)
    mary_start = Int('mary_start')
    mary_end = Int('mary_end')
    
    # Lisa at Mission District: 8:30 PM to 10:00 PM (min 75 minutes)
    lisa_start = Int('lisa_start')
    lisa_end = Int('lisa_end')
    
    # Betty at Haight-Ashbury: 7:15 AM to 5:15 PM (min 90 minutes)
    betty_start = Int('betty_start')
    betty_end = Int('betty_end')
    
    # Charles at Financial District: 11:15 AM to 3:00 PM (min 120 minutes)
    charles_start = Int('charles_start')
    charles_end = Int('charles_end')

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    # Mary's window: 10:00 AM (600) to 7:00 PM (1140) → 60 to 600 minutes after 9:00 AM
    mary_window_start = 60  # 10:00 AM is 60 minutes after 9:00 AM
    mary_window_end = 600    # 7:00 PM is 600 minutes after 9:00 AM
    
    # Lisa's window: 8:30 PM (1230) to 10:00 PM (1320) → 690 to 780 minutes after 9:00 AM
    lisa_window_start = 690  # 8:30 PM is 11.5 hours after 9:00 AM → 690 minutes
    lisa_window_end = 780    # 10:00 PM is 13 hours after 9:00 AM → 780 minutes
    
    # Betty's window: 7:15 AM (435) to 5:15 PM (1035) → -105 to 495 minutes after 9:00 AM
    # But since we start at 9:00 AM, the earliest we can meet is 9:00 AM (0 minutes)
    betty_window_start = 0   # max(0, -105) → 0
    betty_window_end = 495    # 5:15 PM is 8.25 hours after 9:00 AM → 495 minutes
    
    # Charles's window: 11:15 AM (675) to 3:00 PM (900) → 135 to 360 minutes after 9:00 AM
    charles_window_start = 135  # 11:15 AM is 2.25 hours after 9:00 AM → 135 minutes
    charles_window_end = 360    # 3:00 PM is 6 hours after 9:00 AM → 360 minutes

    # Add constraints for each meeting's duration and window
    s.add(mary_start >= mary_window_start)
    s.add(mary_end <= mary_window_end)
    s.add(mary_end - mary_start >= 45)
    
    s.add(lisa_start >= lisa_window_start)
    s.add(lisa_end <= lisa_window_end)
    s.add(lisa_end - lisa_start >= 75)
    
    s.add(betty_start >= betty_window_start)
    s.add(betty_end <= betty_window_end)
    s.add(betty_end - betty_start >= 90)
    
    s.add(charles_start >= charles_window_start)
    s.add(charles_end <= charles_window_end)
    s.add(charles_end - charles_start >= 120)

    # Define variables to indicate whether each meeting is scheduled
    meet_mary = Bool('meet_mary')
    meet_lisa = Bool('meet_lisa')
    meet_betty = Bool('meet_betty')
    meet_charles = Bool('meet_charles')

    # If a meeting is scheduled, its start and end times must be set; otherwise, they are unconstrained beyond the window
    s.add(Implies(meet_mary, And(mary_start >= mary_window_start, mary_end <= mary_window_end, mary_end - mary_start >= 45)))
    s.add(Implies(Not(meet_mary), And(mary_start == 0, mary_end == 0)))  # Dummy values if not meeting
    
    s.add(Implies(meet_lisa, And(lisa_start >= lisa_window_start, lisa_end <= lisa_window_end, lisa_end - lisa_start >= 75)))
    s.add(Implies(Not(meet_lisa), And(lisa_start == 0, lisa_end == 0)))
    
    s.add(Implies(meet_betty, And(betty_start >= betty_window_start, betty_end <= betty_window_end, betty_end - betty_start >= 90)))
    s.add(Implies(Not(meet_betty), And(betty_start == 0, betty_end == 0)))
    
    s.add(Implies(meet_charles, And(charles_start >= charles_window_start, charles_end <= charles_window_end, charles_end - charles_start >= 120)))
    s.add(Implies(Not(meet_charles), And(charles_start == 0, charles_end == 0)))

    # Define travel times
    travel_times = {
        ('bayview', 'haight-ashbury'): 19,
        ('bayview', 'pacific heights'): 23,
        ('bayview', 'financial district'): 19,
        ('bayview', 'mission district'): 13,
        ('haight-ashbury', 'pacific heights'): 12,
        ('haight-ashbury', 'financial district'): 21,
        ('haight-ashbury', 'mission district'): 11,
        ('pacific heights', 'haight-ashbury'): 11,
        ('pacific heights', 'financial district'): 13,
        ('pacific heights', 'mission district'): 15,
        ('financial district', 'haight-ashbury'): 19,
        ('financial district', 'pacific heights'): 13,
        ('financial district', 'mission district'): 17,
        ('mission district', 'haight-ashbury'): 11,
        ('mission district', 'pacific heights'): 16,
        ('mission district', 'financial district'): 17,
    }

    # Define the current location as Bayview at time 0
    current_location = 'bayview'
    current_time = 0

    # Define the sequence of meetings
    sequence = []

    # Define variables for the order of meetings
    order = ['betty', 'mary', 'charles', 'lisa']

    # Define the travel time between meetings
    for i in range(len(order)):
        if i == 0:
            # First meeting: travel from Bayview to the first location
            if order[i] == 'betty':
                travel_time = travel_times[('bayview', 'haight-ashbury')]
                s.add(betty_start == current_time + travel_time)
                s.add(betty_end == betty_start + 90)
                current_time = betty_end
                current_location = 'haight-ashbury'
            elif order[i] == 'mary':
                travel_time = travel_times[('bayview', 'pacific heights')]
                s.add(mary_start == current_time + travel_time)
                s.add(mary_end == mary_start + 45)
                current_time = mary_end
                current_location = 'pacific heights'
            elif order[i] == 'charles':
                travel_time = travel_times[('bayview', 'financial district')]
                s.add(charles_start == current_time + travel_time)
                s.add(charles_end == charles_start + 120)
                current_time = charles_end
                current_location = 'financial district'
            elif order[i] == 'lisa':
                travel_time = travel_times[('bayview', 'mission district')]
                s.add(lisa_start == current_time + travel_time)
                s.add(lisa_end == lisa_start + 75)
                current_time = lisa_end
                current_location = 'mission district'
        else:
            # Subsequent meetings: travel from the previous location to the next location
            if order[i] == 'betty':
                travel_time = travel_times[(current_location, 'haight-ashbury')]
                s.add(betty_start == current_time + travel_time)
                s.add(betty_end == betty_start + 90)
                current_time = betty_end
                current_location = 'haight-ashbury'
            elif order[i] == 'mary':
                travel_time = travel_times[(current_location, 'pacific heights')]
                s.add(mary_start == current_time + travel_time)
                s.add(mary_end == mary_start + 45)
                current_time = mary_end
                current_location = 'pacific heights'
            elif order[i] == 'charles':
                travel_time = travel_times[(current_location, 'financial district')]
                s.add(charles_start == current_time + travel_time)
                s.add(charles_end == charles_start + 120)
                current_time = charles_end
                current_location = 'financial district'
            elif order[i] == 'lisa':
                travel_time = travel_times[(current_location, 'mission district')]
                s.add(lisa_start == current_time + travel_time)
                s.add(lisa_end == lisa_start + 75)
                current_time = lisa_end
                current_location = 'mission district'

    # Maximize the number of friends met
    s.maximize(If(meet_mary, 1, 0) + If(meet_lisa, 1, 0) + If(meet_betty, 1, 0) + If(meet_charles, 1, 0))

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        if is_true(m[meet_betty]):
            start = m[betty_start].as_long()
            end = m[betty_end].as_long()
            itinerary.append({"action": "meet", "person": "Betty", "start_time": f"{start // 60 + 9:02d}:{start % 60:02d}", "end_time": f"{end // 60 + 9:02d}:{end % 60:02d}"})
        
        if is_true(m[meet_mary]):
            start = m[mary_start].as_long()
            end = m[mary_end].as_long()
            itinerary.append({"action": "meet", "person": "Mary", "start_time": f"{start // 60 + 9:02d}:{start % 60:02d}", "end_time": f"{end // 60 + 9:02d}:{end % 60:02d}"})
        
        if is_true(m[meet_charles]):
            start = m[charles_start].as_long()
            end = m[charles_end].as_long()
            itinerary.append({"action": "meet", "person": "Charles", "start_time": f"{start // 60 + 9:02d}:{start % 60:02d}", "end_time": f"{end // 60 + 9:02d}:{end % 60:02d}"})
        
        if is_true(m[meet_lisa]):
            start = m[lisa_start].as_long()
            end = m[lisa_end].as_long()
            itinerary.append({"action": "meet", "person": "Lisa", "start_time": f"{start // 60 + 9:02d}:{start % 60:02d}", "end_time": f"{end // 60 + 9:02d}:{end % 60:02d}"})
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling()
print(json.dumps(solution, indent=2))