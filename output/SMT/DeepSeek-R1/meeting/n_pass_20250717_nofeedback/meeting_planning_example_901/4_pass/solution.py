from z3 import *

def main():
    # Time in minutes from midnight
    persons = ['Emily', 'Nancy', 'Margaret', 'Helen', 'Linda', 'William', 'Kimberly']
    start = {p: Int(f'start_{p}') for p in persons}
    dur = {p: Int(f'dur_{p}') for p in persons}
    
    s = Solver()
    
    # Global time window [09:00, 21:30] -> 540 to 1290 minutes
    for p in persons:
        s.add(start[p] >= 540)
        s.add(start[p] + dur[p] <= 1290)
        s.add(dur[p] >= 15)
        s.add(dur[p] <= 120)
    
    # William's meeting between 17:00 (1020) and 20:00 (1200)
    s.add(start['William'] >= 1020)
    s.add(start['William'] + dur['William'] <= 1200)
    
    # Kimberly's meeting between 19:00 (1140) and 21:30 (1290)
    s.add(start['Kimberly'] >= 1140)
    s.add(start['Kimberly'] + dur['Kimberly'] <= 1290)
    
    # Kimberly must start at least 60 minutes after William ends
    s.add(start['Kimberly'] >= start['William'] + dur['William'] + 60)
    
    # Linda must start at least 30 minutes before William and end by the time William starts
    s.add(start['Linda'] <= start['William'] - 30)
    s.add(start['Linda'] + dur['Linda'] <= start['William'])
    
    # Helen and Linda must be at least 60 minutes apart
    s.add(Or(
        start['Linda'] >= start['Helen'] + dur['Helen'] + 60,
        start['Helen'] >= start['Linda'] + dur['Linda'] + 60
    ))
    
    # For every pair of meetings, ensure at least 10 minutes gap (travel time)
    pairs = []
    for i in range(len(persons)):
        for j in range(i+1, len(persons)):
            p1 = persons[i]
            p2 = persons[j]
            gap = 10
            s.add(Or(
                start[p1] + dur[p1] + gap <= start[p2],
                start[p2] + dur[p2] + gap <= start[p1]
            ))
    
    if s.check() == sat:
        model = s.model()
        schedule = []
        for p in persons:
            s_val = model.eval(start[p]).as_long()
            d_val = model.eval(dur[p]).as_long()
            start_hour = s_val // 60
            start_minute = s_val % 60
            end_time = s_val + d_val
            end_hour = end_time // 60
            end_minute = end_time % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            schedule.append((p, start_str, end_str))
        
        # Sort by start time
        schedule.sort(key=lambda x: x[1])
        
        itinerary = []
        for (p, st, et) in schedule:
            itinerary.append({'action': 'meet', 'person': p, 'start_time': st, 'end_time': et})
        
        print(f"Plan found: {{'itinerary': {itinerary}}}")
    else:
        print("No valid plan found.")

if __name__ == '__main__':
    main()