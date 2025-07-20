from z3 import *
import datetime

# Define travel times (minutes)
travel = {
    'Bayview': {'Union Square': 17, 'Presidio': 31},
    'Union Square': {'Bayview': 15, 'Presidio': 24},
    'Presidio': {'Bayview': 31, 'Union Square': 22}
}

# Friend availability
friends = {
    'Richard': {
        'location': 'Union Square',
        'start': datetime.time(8, 45),
        'end': datetime.time(13, 0),
        'duration': 120
    },
    'Charles': {
        'location': 'Presidio',
        'start': datetime.time(9, 45),
        'end': datetime.time(13, 0),
        'duration': 120
    }
}

# Convert time to minutes since 9:00 AM
def time_to_minutes(t):
    base = datetime.datetime.combine(datetime.date.today(), datetime.time(9, 0))
    current = datetime.datetime.combine(datetime.date.today(), t)
    return int((current - base).total_seconds() / 60)

# Convert minutes back to time
def minutes_to_time(m):
    base = datetime.datetime.combine(datetime.date.today(), datetime.time(9, 0))
    delta = datetime.timedelta(minutes=m)
    return (base + delta).time().strftime("%H:%M")

# Initialize solver
s = Solver()

# Create meeting time variables
meetings = {}
for name in friends:
    meetings[name] = {
        'start': Int(f'start_{name}'),
        'end': Int(f'end_{name}')
    }

# Add constraints for each friend
for name, info in friends.items():
    start = meetings[name]['start']
    end = meetings[name]['end']
    available_start = time_to_minutes(info['start'])
    available_end = time_to_minutes(info['end'])
    duration = info['duration']
    
    s.add(start >= available_start)
    s.add(end <= available_end)
    s.add(end - start >= duration)
    s.add(start < end)

# Try both possible meeting orders
def try_order(order):
    temp_s = Solver()
    temp_s.add(s.assertions())
    
    current_loc = 'Bayview'
    current_time = 0  # 9:00 AM
    
    for i, name in enumerate(order):
        dest = friends[name]['location']
        travel_time = travel[current_loc][dest]
        
        # Must arrive at destination before meeting starts
        temp_s.add(meetings[name]['start'] >= current_time + travel_time)
        
        # Update current location and time
        current_loc = dest
        current_time = meetings[name]['end']
        
        # If there's another meeting, add travel constraint
        if i < len(order) - 1:
            next_dest = friends[order[i+1]]['location']
            next_travel = travel[current_loc][next_dest]
            temp_s.add(meetings[order[i+1]]['start'] >= current_time + next_travel)
    
    if temp_s.check() == sat:
        return temp_s.model()
    return None

# Try Richard first, then Charles
model = try_order(['Richard', 'Charles']) or try_order(['Charles', 'Richard'])

if model:
    itinerary = []
    for name in friends:
        start = model[meetings[name]['start']].as_long()
        end = model[meetings[name]['end']].as_long()
        itinerary.append({
            'action': 'meet',
            'person': name,
            'start_time': minutes_to_time(start),
            'end_time': minutes_to_time(end)
        })
    
    # Sort by start time
    itinerary.sort(key=lambda x: x['start_time'])
    
    print('SOLUTION:')
    print({"itinerary": itinerary})
else:
    print("No valid schedule found that meets all constraints")