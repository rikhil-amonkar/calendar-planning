from z3 import *

def main():
    persons = ['Emily', 'Nancy', 'Margaret', 'Helen', 'Linda', 'William', 'Kimberly']
    n = len(persons)
    start = {p: Int(f'start_{p}') for p in persons}
    dur = {p: Int(f'dur_{p}') for p in persons}
    end = {p: start[p] + dur[p] for p in persons}
    
    s = Solver()
    
    # Convert times to minutes (09:00=540, 21:30=1290)
    for p in persons:
        s.add(start[p] >= 540)     # 09:00
        s.add(end[p] <= 1290)       # 21:30
        s.add(dur[p] >= 15)         # Minimum duration
        s.add(dur[p] <= 120)        # Maximum duration
    
    # William's meeting (17:00-20:00)
    s.add(start['William'] >= 1020)  # 17:00
    s.add(end['William'] <= 1200)    # 20:00
    
    # Kimberly's meeting (19:00-21:30)
    s.add(start['Kimberly'] >= 1140)  # 19:00
    s.add(end['Kimberly'] <= 1290)    # 21:30
    
    # Kimberly starts at least 60min after William ends
    s.add(start['Kimberly'] >= end['William'] + 60)
    
    # Linda starts >=30min before William and ends when William starts
    s.add(start['Linda'] <= start['William'] - 30)
    s.add(end['Linda'] <= start['William'])
    
    # Helen and Linda are at least 60min apart
    s.add(Or(
        start['Linda'] >= end['Helen'] + 60,
        start['Helen'] >= end['Linda'] + 60
    ))
    
    # Define meeting order
    order = IntVector('order', n)
    s.add(Distinct(order))
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    
    # Travel time between consecutive meetings
    for k in range(n-1):
        or_conditions = []
        for i in range(n):
            for j in range(n):
                if i == j:
                    continue
                cond = And(
                    order[i] == k,
                    order[j] == k + 1,
                    end[persons[i]] + 10 <= start[persons[j]]
                )
                or_conditions.append(cond)
        s.add(Or(or_conditions))
    
    if s.check() == sat:
        m = s.model()
        schedule = []
        for p in persons:
            s_val = m.eval(start[p]).as_long()
            d_val = m.eval(dur[p]).as_long()
            start_time = f"{s_val//60:02d}:{s_val%60:02d}"
            end_time = f"{(s_val+d_val)//60:02d}:{(s_val+d_val)%60:02d}"
            schedule.append((p, start_time, end_time))
        schedule.sort(key=lambda x: x[1])
        itinerary = [{'action': 'meet', 'person': p, 'start_time': st, 'end_time': et} 
                    for p, st, et in schedule]
        print(f"Plan found: {{'itinerary': {itinerary}}}")
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()