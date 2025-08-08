from z3 import *
import json

def find_contiguous_blocks(days_list):
    if not days_list:
        return []
    days_list.sort()
    blocks = []
    start = days_list[0]
    end = days_list[0]
    for i in range(1, len(days_list)):
        if days_list[i] == end + 1:
            end = days_list[i]
        else:
            blocks.append((start, end))
            start = days_list[i]
            end = days_list[i]
    blocks.append((start, end))
    return blocks

def main():
    days = 7
    R = [Bool(f'R_{i}') for i in range(days)]
    A = [Bool(f'A_{i}') for i in range(days)]
    M = [Bool(f'M_{i}') for i in range(days)]
    
    s = Solver()
    
    for i in range(days):
        s.add(Or(R[i], A[i], M[i]))
        s.add(Not(And(R[i], A[i], M[i])))
        s.add(Not(And(R[i], M[i])))
    
    for i in range(days - 1):
        s.add(Or(
            And(R[i], R[i+1]),
            And(A[i], A[i+1]),
            And(M[i], M[i+1])
        ))
    
    s.add(R[0] == True)
    s.add(R[1] == True)
    s.add(Sum([If(R[i], 1, 0) for i in range(days)]) == 2)
    
    s.add(Sum([If(A[i], 1, 0) for i in range(days)]) == 2)
    s.add(Sum([If(M[i], 1, 0) for i in range(days)]) == 5)
    
    if s.check() == sat:
        m = s.model()
        riga_days = []
        amsterdam_days = []
        mykonos_days = []
        
        for i in range(days):
            if m.evaluate(R[i]) == True:
                riga_days.append(i)
            if m.evaluate(A[i]) == True:
                amsterdam_days.append(i)
            if m.evaluate(M[i]) == True:
                mykonos_days.append(i)
        
        riga_blocks = find_contiguous_blocks(riga_days)
        amsterdam_blocks = find_contiguous_blocks(amsterdam_days)
        mykonos_blocks = find_contiguous_blocks(mykonos_days)
        
        itinerary = []
        for block in riga_blocks:
            start_day = block[0] + 1
            end_day = block[1] + 1
            day_range = f"Day {start_day}-{end_day}" if start_day != end_day else f"Day {start_day}-{start_day}"
            itinerary.append({'day_range': day_range, 'place': 'Riga'})
        
        for block in amsterdam_blocks:
            start_day = block[0] + 1
            end_day = block[1] + 1
            day_range = f"Day {start_day}-{end_day}" if start_day != end_day else f"Day {start_day}-{start_day}"
            itinerary.append({'day_range': day_range, 'place': 'Amsterdam'})
        
        for block in mykonos_blocks:
            start_day = block[0] + 1
            end_day = block[1] + 1
            day_range = f"Day {start_day}-{end_day}" if start_day != end_day else f"Day {start_day}-{start_day}"
            itinerary.append({'day_range': day_range, 'place': 'Mykonos'})
        
        itinerary.sort(key=lambda x: int(x['day_range'].split(' ')[1].split('-')[0]))
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({'error': 'No solution found'}))

if __name__ == '__main__':
    main()