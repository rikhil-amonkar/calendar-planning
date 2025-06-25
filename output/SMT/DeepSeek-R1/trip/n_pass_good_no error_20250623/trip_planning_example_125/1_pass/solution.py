import json
from z3 import *

def main():
    s_start, s_end, m_start, m_end, v_start, v_end = Ints('s_start s_end m_start m_end v_start v_end')
    
    solver = Solver()
    
    solver.add(s_start == 1)
    solver.add(v_end == 15)
    solver.add(s_end == m_start)
    solver.add(m_end == v_start)
    solver.add(s_end - s_start + 1 == 6)
    solver.add(m_end - m_start + 1 == 4)
    solver.add(v_end - v_start + 1 == 7)
    
    solver.add(s_start >= 1, s_end <= 15)
    solver.add(m_start >= 1, m_end <= 15)
    solver.add(v_start >= 1, v_end <= 15)
    solver.add(s_start <= s_end, m_start <= m_end, v_start <= v_end)
    
    events = []
    if solver.check() == sat:
        model = solver.model()
        s_start_val = model[s_start].as_long()
        s_end_val = model[s_end].as_long()
        m_start_val = model[m_start].as_long()
        m_end_val = model[m_end].as_long()
        v_start_val = model[v_start].as_long()
        v_end_val = model[v_end].as_long()
        
        events.append({"day_range": f"Day {s_start_val}-{s_end_val}", "place": "Stuttgart"})
        events.append({"day_range": f"Day {s_end_val}", "place": "Stuttgart"})
        events.append({"day_range": f"Day {s_end_val}", "place": "Manchester"})
        events.append({"day_range": f"Day {m_start_val}-{m_end_val}", "place": "Manchester"})
        events.append({"day_range": f"Day {m_end_val}", "place": "Manchester"})
        events.append({"day_range": f"Day {m_end_val}", "place": "Seville"})
        events.append({"day_range": f"Day {v_start_val}-{v_end_val}", "place": "Seville"})
    
    result = {"itinerary": events}
    print(json.dumps(result))

if __name__ == "__main__":
    main()