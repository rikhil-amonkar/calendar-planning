from z3 import *
import json

def solve_scheduling():
    s = Optimize()

    # Define meeting variables (start and end times in minutes since 9:00 AM)
    mary_start, mary_end = Int('mary_start'), Int('mary_end')
    lisa_start, lisa_end = Int('lisa_start'), Int('lisa_end')
    betty_start, betty_end = Int('betty_start'), Int('betty_end')
    charles_start, charles_end = Int('charles_start'), Int('charles_end')

    # Define time windows (minutes since 9:00 AM)
    mary_window = (60, 600)    # 10:00 AM to 7:00 PM
    lisa_window = (690, 780)   # 8:30 PM to 10:00 PM
    betty_window = (0, 495)    # 9:00 AM to 5:15 PM
    charles_window = (135, 360) # 11:15 AM to 3:00 PM

    # Meeting duration constraints
    s.add(mary_end - mary_start >= 45)
    s.add(lisa_end - lisa_start >= 75)
    s.add(betty_end - betty_start >= 90)
    s.add(charles_end - charles_start >= 120)

    # Time window constraints
    s.add(And(mary_start >= mary_window[0], mary_end <= mary_window[1]))
    s.add(And(lisa_start >= lisa_window[0], lisa_end <= lisa_window[1]))
    s.add(And(betty_start >= betty_window[0], betty_end <= betty_window[1]))
    s.add(And(charles_start >= charles_window[0], charles_end <= charles_window[1]))

    # Define travel times between locations
    travel = {
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

    # Define meeting flags
    meet_mary = Bool('meet_mary')
    meet_lisa = Bool('meet_lisa')
    meet_betty = Bool('meet_betty')
    meet_charles = Bool('meet_charles')

    # Only enforce constraints if meeting is scheduled
    s.add(Implies(meet_mary, And(mary_start >= mary_window[0], mary_end <= mary_window[1], mary_end - mary_start >= 45)))
    s.add(Implies(meet_lisa, And(lisa_start >= lisa_window[0], lisa_end <= lisa_window[1], lisa_end - lisa_start >= 75)))
    s.add(Implies(meet_betty, And(betty_start >= betty_window[0], betty_end <= betty_window[1], betty_end - betty_start >= 90)))
    s.add(Implies(meet_charles, And(charles_start >= charles_window[0], charles_end <= charles_window[1], charles_end - charles_start >= 120)))

    # Define possible meeting orders
    orders = [
        ['betty', 'mary', 'charles'],
        ['betty', 'charles', 'mary'],
        ['mary', 'betty', 'charles'],
        ['mary', 'charles', 'betty'],
        ['charles', 'betty', 'mary'],
        ['charles', 'mary', 'betty']
    ]

    # Try different meeting orders
    for order in orders:
        # Reset solver for each order
        temp_s = Solver()
        temp_s.add(s.assertions())

        # Track current location and time
        current_loc = 'bayview'
        current_time = 0

        # Schedule meetings in order
        for person in order:
            if person == 'betty':
                travel_time = travel[(current_loc, 'haight-ashbury')]
                temp_s.add(betty_start == current_time + travel_time)
                temp_s.add(betty_end == betty_start + 90)
                current_time = betty_end
                current_loc = 'haight-ashbury'
                temp_s.add(meet_betty == True)
            elif person == 'mary':
                travel_time = travel[(current_loc, 'pacific heights')]
                temp_s.add(mary_start == current_time + travel_time)
                temp_s.add(mary_end == mary_start + 45)
                current_time = mary_end
                current_loc = 'pacific heights'
                temp_s.add(meet_mary == True)
            elif person == 'charles':
                travel_time = travel[(current_loc, 'financial district')]
                temp_s.add(charles_start == current_time + travel_time)
                temp_s.add(charles_end == charles_start + 120)
                current_time = charles_end
                current_loc = 'financial district'
                temp_s.add(meet_charles == True)

        # Try to schedule Lisa at the end if possible
        travel_time = travel[(current_loc, 'mission district')]
        temp_s.add(Implies(meet_lisa, And(
            lisa_start == current_time + travel_time,
            lisa_end == lisa_start + 75,
            lisa_end <= lisa_window[1]
        )))

        # Maximize number of meetings
        temp_s.maximize(
            If(meet_mary, 1, 0) + 
            If(meet_lisa, 1, 0) + 
            If(meet_betty, 1, 0) + 
            If(meet_charles, 1, 0)
        )

        if temp_s.check() == sat:
            m = temp_s.model()
            itinerary = []
            
            if is_true(m[meet_betty]):
                start = m[betty_start].as_long()
                end = m[betty_end].as_long()
                itinerary.append({
                    "action": "meet", 
                    "person": "Betty", 
                    "start_time": f"{(start // 60 + 9):02d}:{(start % 60):02d}", 
                    "end_time": f"{(end // 60 + 9):02d}:{(end % 60):02d}"
                })
            
            if is_true(m[meet_mary]):
                start = m[mary_start].as_long()
                end = m[mary_end].as_long()
                itinerary.append({
                    "action": "meet", 
                    "person": "Mary", 
                    "start_time": f"{(start // 60 + 9):02d}:{(start % 60):02d}", 
                    "end_time": f"{(end // 60 + 9):02d}:{(end % 60):02d}"
                })
            
            if is_true(m[meet_charles]):
                start = m[charles_start].as_long()
                end = m[charles_end].as_long()
                itinerary.append({
                    "action": "meet", 
                    "person": "Charles", 
                    "start_time": f"{(start // 60 + 9):02d}:{(start % 60):02d}", 
                    "end_time": f"{(end // 60 + 9):02d}:{(end % 60):02d}"
                })
            
            if is_true(m[meet_lisa]):
                start = m[lisa_start].as_long()
                end = m[lisa_end].as_long()
                itinerary.append({
                    "action": "meet", 
                    "person": "Lisa", 
                    "start_time": f"{(start // 60 + 9):02d}:{(start % 60):02d}", 
                    "end_time": f"{(end // 60 + 9):02d}:{(end % 60):02d}"
                })
            
            return {"itinerary": itinerary}

    return {"itinerary": []}

solution = solve_scheduling()
print(json.dumps(solution, indent=2))