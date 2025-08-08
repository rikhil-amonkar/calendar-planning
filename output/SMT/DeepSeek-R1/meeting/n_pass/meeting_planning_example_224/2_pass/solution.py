from z3 import *

def min_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def main():
    opt = Optimize()
    
    m_start = Int('m_start')
    m_end = m_start + 15
    
    e_start = Int('e_start')
    e_end = e_start + 120
    
    n_start = Int('n_start')
    n_end = n_start + 105
    
    opt.add(m_start >= 565)
    opt.add(m_end <= 1200)
    
    opt.add(e_start >= 1005)
    opt.add(e_start >= m_end + 7)
    opt.add(e_end <= 1320)
    
    opt.add(n_start >= 1185)
    opt.add(n_start >= e_end + 7)
    opt.add(n_end <= 1320)
    
    waiting1 = e_start - (m_end + 7)
    waiting2 = n_start - (e_end + 7)
    total_waiting = waiting1 + waiting2
    
    opt.minimize(total_waiting)
    
    if opt.check() == sat:
        model = opt.model()
        m_val = model[m_start].as_long()
        e_val = model[e_start].as_long()
        n_val = model[n_start].as_long()
        
        itinerary = [
            {"action": "meet", "person": "Melissa", "start_time": min_to_time(m_val), "end_time": min_to_time(m_val + 15)},
            {"action": "meet", "person": "Emily", "start_time": min_to_time(e_val), "end_time": min_to_time(e_val + 120)},
            {"action": "meet", "person": "Nancy", "start_time": min_to_time(n_val), "end_time": min_to_time(n_val + 105)}
        ]
        result = {"itinerary": itinerary}
        print(result)
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()