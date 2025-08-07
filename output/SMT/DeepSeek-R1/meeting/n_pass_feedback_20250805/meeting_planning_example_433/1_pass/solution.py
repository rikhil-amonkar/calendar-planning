import z3
import itertools
from z3 import Int, Solver, Distinct, If, And

def main():
    meetings = [
        (0, 'Jeffrey', 120, 135, 330, 'Golden Gate Park'),
        (1, 'Margaret', 75, 450, 675, 'Financial District'),
        (2, 'Ronald', 45, 570, 630, 'North Beach'),
        (3, 'Deborah', 90, 285, 735, 'The Castro'),
        (4, 'Emily', 15, 600, 720, 'Richmond District')
    ]
    
    travel_dict = {
        'Nob Hill': {
            'Richmond District': 14,
            'Financial District': 9,
            'North Beach': 8,
            'The Castro': 17,
            'Golden Gate Park': 17
        },
        'Richmond District': {
            'Nob Hill': 17,
            'Financial District': 22,
            'North Beach': 17,
            'The Castro': 16,
            'Golden Gate Park': 9
        },
        'Financial District': {
            'Nob Hill': 8,
            'Richmond District': 21,
            'North Beach': 7,
            'The Castro': 23,
            'Golden Gate Park': 23
        },
        'North Beach': {
            'Nob Hill': 7,
            'Richmond District': 18,
            'Financial District': 8,
            'The Castro': 22,
            'Golden Gate Park': 22
        },
        'The Castro': {
            'Nob Hill': 16,
            'Richmond District': 16,
            'Financial District': 20,
            'North Beach': 20,
            'Golden Gate Park': 11
        },
        'Golden Gate Park': {
            'Nob Hill': 20,
            'Richmond District': 7,
            'Financial District': 26,
            'North Beach': 24,
            'The Castro': 13
        }
    }
    
    n = len(meetings)
    s = Solver()
    
    T = [Int(f'T_{i}') for i in range(n)]
    M = [Int(f'M_{i}') for i in range(n)]
    
    s.add(Distinct(M))
    for i in range(n):
        s.add(M[i] >= 0)
        s.add(M[i] < n)
        
    for i in range(n):
        s.add(T[i] >= meetings[i][3])
        s.add(T[i] + meetings[i][2] <= meetings[i][4])
        s.add(T[i] >= 0)
        
    for i in range(n):
        s.add(If(M[0] == i, T[i] >= travel_dict['Nob Hill'][meetings[i][5]], True))
        
    for k in range(0, n-1):
        for i in range(n):
            for j in range(n):
                if i == j:
                    continue
                s.add(If(And(M[k] == i, M[k+1] == j),
                          T[j] >= T[i] + meetings[i][2] + travel_dict[meetings[i][5]][meetings[j][5]],
                          True))
    
    if s.check() == z3.sat:
        model = s.model()
        schedule = []
        for i in range(n):
            t_val = model.evaluate(T[i])
            start_minutes = t_val.as_long()
            total_minutes = start_minutes
            hour = total_minutes // 60
            minute = total_minutes % 60
            start_time = f"{9 + hour:02d}:{minute:02d}"
            
            end_minutes = start_minutes + meetings[i][2]
            end_hour = end_minutes // 60
            end_minute = end_minutes % 60
            end_time = f"{9 + end_hour:02d}:{end_minute:02d}"
            
            schedule.append({
                "action": "meet",
                "person": meetings[i][1],
                "start_time": start_time,
                "end_time": end_time
            })
        
        schedule_sorted = sorted(schedule, key=lambda x: x['start_time'])
        print(f'{{"itinerary": {schedule_sorted}}}')
    else:
        print('No solution found for all meetings.')

if __name__ == '__main__':
    main()