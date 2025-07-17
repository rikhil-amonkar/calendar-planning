from z3 import *

def solve_scheduling():
    s = Solver()

    # Define time variables in minutes since 9:00 AM
    carol_start = Int('carol_start')
    carol_end = Int('carol_end')
    rebecca_start = Int('rebecca_start')
    rebecca_end = Int('rebecca_end')
    karen_start = Int('karen_start')
    karen_end = Int('karen_end')

    # Time windows in minutes since 9:00 AM
    carol_window = (75, 165)    # 10:15-11:45
    rebecca_window = (150, 675) # 11:30-20:15
    karen_window = (225, 360)   # 12:45-15:00

    # Minimum meeting durations
    carol_min = 30
    rebecca_min = 120
    karen_min = 120

    # Travel times between locations (minutes)
    travel = {
        ('Union Square', 'Sunset District'): 26,
        ('Sunset District', 'Mission District'): 24,
        ('Mission District', 'Bayview'): 15,
        ('Union Square', 'Mission District'): 14,
        ('Mission District', 'Union Square'): 15,
        ('Union Square', 'Bayview'): 15,
        ('Bayview', 'Mission District'): 13,
        ('Sunset District', 'Bayview'): 22,
        ('Bayview', 'Sunset District'): 23,
        ('Mission District', 'Sunset District'): 24,
        ('Bayview', 'Union Square'): 17,
        ('Sunset District', 'Union Square'): 30
    }

    # Try different meeting orders
    orders = [
        ['Carol', 'Rebecca', 'Karen'],  # Sunset -> Mission -> Bayview
        ['Rebecca', 'Karen', 'Carol'],  # Mission -> Bayview -> Sunset
        ['Rebecca', 'Carol', 'Karen'],  # Mission -> Sunset -> Bayview
        ['Carol', 'Karen', 'Rebecca'],  # Sunset -> Bayview -> Mission
        ['Karen', 'Rebecca', 'Carol'],  # Bayview -> Mission -> Sunset
        ['Karen', 'Carol', 'Rebecca']   # Bayview -> Sunset -> Mission
    ]

    for order in orders:
        s.push()
        
        # Set up meeting variables based on order
        meetings = []
        for i, person in enumerate(order):
            if person == 'Carol':
                meetings.append(('Carol', carol_start, carol_end, carol_window, carol_min))
            elif person == 'Rebecca':
                meetings.append(('Rebecca', rebecca_start, rebecca_end, rebecca_window, rebecca_min))
            elif person == 'Karen':
                meetings.append(('Karen', karen_start, karen_end, karen_window, karen_min))
        
        # Add constraints for each meeting
        for person, start, end, window, min_dur in meetings:
            s.add(start >= window[0])
            s.add(end <= window[1])
            s.add(end - start >= min_dur)
        
        # Add travel time constraints between meetings
        for i in range(len(meetings)-1):
            current_person = meetings[i][0]
            next_person = meetings[i+1][0]
            
            # Determine travel time between current and next location
            if current_person == 'Carol' and next_person == 'Rebecca':
                travel_time = travel[('Sunset District', 'Mission District')]
            elif current_person == 'Carol' and next_person == 'Karen':
                travel_time = travel[('Sunset District', 'Bayview')]
            elif current_person == 'Rebecca' and next_person == 'Karen':
                travel_time = travel[('Mission District', 'Bayview')]
            elif current_person == 'Rebecca' and next_person == 'Carol':
                travel_time = travel[('Mission District', 'Sunset District')]
            elif current_person == 'Karen' and next_person == 'Rebecca':
                travel_time = travel[('Bayview', 'Mission District')]
            elif current_person == 'Karen' and next_person == 'Carol':
                travel_time = travel[('Bayview', 'Sunset District')]
            
            s.add(meetings[i+1][1] >= meetings[i][2] + travel_time)
        
        # First meeting must account for travel from Union Square
        first_person = meetings[0][0]
        if first_person == 'Carol':
            s.add(meetings[0][1] >= travel[('Union Square', 'Sunset District')])
        elif first_person == 'Rebecca':
            s.add(meetings[0][1] >= travel[('Union Square', 'Mission District')])
        elif first_person == 'Karen':
            s.add(meetings[0][1] >= travel[('Union Square', 'Bayview')])
        
        if s.check() == sat:
            m = s.model()
            
            def to_time(minutes):
                h = (540 + minutes) // 60
                m = (540 + minutes) % 60
                return f"{h:02d}:{m:02d}"
            
            itinerary = []
            for person, start, end, _, _ in meetings:
                s_time = m.eval(start).as_long()
                e_time = m.eval(end).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": person,
                    "start_time": to_time(s_time),
                    "end_time": to_time(e_time)
                })
            
            return {"itinerary": itinerary}
        
        s.pop()
    
    return {"itinerary": []}

solution = solve_scheduling()
print(solution)