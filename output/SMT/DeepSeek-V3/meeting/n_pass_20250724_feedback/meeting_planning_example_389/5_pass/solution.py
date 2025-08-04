from z3 import *
import datetime

def solve_scheduling():
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes)
    def time_to_min(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m - 540  # Subtract 9:00 AM (540 minutes)

    # Meeting variables (in minutes since 9:00 AM)
    mary_start = Int('mary_start')
    mary_end = Int('mary_end')
    sarah_start = Int('sarah_start')
    sarah_end = Int('sarah_end')
    thomas_start = Int('thomas_start')
    thomas_end = Int('thomas_end')
    helen_start = Int('helen_start')
    helen_end = Int('helen_end')

    # Time windows (converted to minutes since 9:00 AM)
    # Mary: 1:00 PM to 7:15 PM (240 to 615 minutes)
    s.add(mary_start >= 240)
    s.add(mary_end <= 615)
    s.add(mary_end == mary_start + 75)  # 75 minute duration

    # Sarah: 2:45 PM to 5:30 PM (345 to 510 minutes)
    s.add(sarah_start >= 345)
    s.add(sarah_end <= 510)
    s.add(sarah_end == sarah_start + 105)  # 105 minute duration

    # Thomas: 3:15 PM to 6:45 PM (375 to 585 minutes)
    s.add(thomas_start >= 375)
    s.add(thomas_end <= 585)
    s.add(thomas_end == thomas_start + 120)  # 120 minute duration

    # Helen: 9:45 PM to 10:30 PM (765 to 810 minutes)
    s.add(helen_start >= 765)
    s.add(helen_end <= 810)
    s.add(helen_end == helen_start + 30)  # 30 minute duration

    # Travel times between locations (in minutes)
    travel = {
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Bayview'): 26,
        ('Richmond District', 'Mission District'): 20,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Bayview', 'Mission District'): 13,
    }

    # Define possible meeting sequences
    # We'll try different orders to find a feasible schedule
    sequences = [
        ['Mary', 'Sarah', 'Thomas', 'Helen'],
        ['Mary', 'Thomas', 'Sarah', 'Helen'],
        ['Sarah', 'Mary', 'Thomas', 'Helen'],
        ['Sarah', 'Thomas', 'Mary', 'Helen'],
        ['Thomas', 'Mary', 'Sarah', 'Helen'],
        ['Thomas', 'Sarah', 'Mary', 'Helen'],
    ]

    for seq in sequences:
        s.push()  # Save current solver state
        
        # Add sequence constraints
        prev_location = 'Haight-Ashbury'
        prev_end = 0  # Starting at 9:00 AM (time 0)
        
        for person in seq:
            if person == 'Mary':
                s.add(mary_start >= prev_end + travel[(prev_location, 'Richmond District')])
                prev_end = mary_end
                prev_location = 'Richmond District'
            elif person == 'Sarah':
                s.add(sarah_start >= prev_end + travel[(prev_location, 'Fisherman\'s Wharf')])
                prev_end = sarah_end
                prev_location = 'Fisherman\'s Wharf'
            elif person == 'Thomas':
                s.add(thomas_start >= prev_end + travel[(prev_location, 'Bayview')])
                prev_end = thomas_end
                prev_location = 'Bayview'
            elif person == 'Helen':
                s.add(helen_start >= prev_end + travel[(prev_location, 'Mission District')])
                prev_end = helen_end
                prev_location = 'Mission District'
        
        if s.check() == sat:
            model = s.model()
            
            def min_to_time(minutes):
                time = datetime.datetime.strptime("09:00", "%H:%M") + datetime.timedelta(minutes=minutes)
                return time.strftime("%H:%M")
            
            itinerary = []
            for person in seq:
                if person == 'Mary':
                    itinerary.append({
                        "action": "meet",
                        "person": "Mary",
                        "start_time": min_to_time(model[mary_start].as_long()),
                        "end_time": min_to_time(model[mary_end].as_long())
                    })
                elif person == 'Sarah':
                    itinerary.append({
                        "action": "meet",
                        "person": "Sarah",
                        "start_time": min_to_time(model[sarah_start].as_long()),
                        "end_time": min_to_time(model[sarah_end].as_long())
                    })
                elif person == 'Thomas':
                    itinerary.append({
                        "action": "meet",
                        "person": "Thomas",
                        "start_time": min_to_time(model[thomas_start].as_long()),
                        "end_time": min_to_time(model[thomas_end].as_long())
                    })
                elif person == 'Helen':
                    itinerary.append({
                        "action": "meet",
                        "person": "Helen",
                        "start_time": min_to_time(model[helen_start].as_long()),
                        "end_time": min_to_time(model[helen_end].as_long())
                    })
            
            return {"itinerary": itinerary}
        else:
            s.pop()  # Restore solver state
    
    return {"error": "No feasible schedule found"}

result = solve_scheduling()
print(result)