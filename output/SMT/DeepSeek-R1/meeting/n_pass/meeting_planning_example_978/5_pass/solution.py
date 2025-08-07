from z3 import *

def main():
    meetings = [
        (0, "Lisa", 15, "A"),
        (1, "Joshua", 15, "B"),
        (2, "Joseph", 45, "C"),
        (3, "Betty", 60, "D"),
        (4, "John", 45, "E"),
        (5, "Sarah", 105, "F"),
        (6, "Daniel", 60, "G"),
        (7, "Melissa", 120, "H"),
        (8, "Andrew", 105, "I")
    ]
    
    adjacencies = {
        "A": ["B", "D"],
        "B": ["A", "C"],
        "C": ["B", "D"],
        "D": ["A", "C", "E", "G"],
        "E": ["D", "F"],
        "F": ["E", "G"],
        "G": ["D", "F", "H", "I"],
        "H": ["G", "I"],
        "I": ["G", "H"]
    }
    
    names = [m[1] for m in meetings]
    durations = [m[2] for m in meetings]
    buildings = [m[3] for m in meetings]
    
    n = len(meetings)
    travel_matrix = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i == j:
                travel_matrix[i][j] = 0
            else:
                b1 = buildings[i]
                b2 = buildings[j]
                if b1 == b2:
                    travel_matrix[i][j] = 0
                elif b2 in adjacencies[b1]:
                    travel_matrix[i][j] = 15
                else:
                    travel_matrix[i][j] = 30
    
    s = Solver()
    s.set("timeout", 300000)
    
    # Create array mapping position to meeting index
    pos_to_meeting = Array('pos_to_meeting', IntSort(), IntSort())
    
    # Create variables for start times
    start = [Int(f'start_{i}') for i in range(n)]
    
    # Constraints for start times
    for i in range(n):
        s.add(start[i] >= 0, start[i] + durations[i] <= 720)
    
    # Specific time constraints
    s.add(start[4] >= 180)   # John after 13:00
    s.add(start[8] <= 585)   # Andrew by 19:45
    
    # Each position 0 to n-1 is assigned a meeting
    for p in range(n):
        meeting_idx = Int(f'mt_at_pos_{p}')
        s.add(meeting_idx >= 0, meeting_idx < n)
        s.add(pos_to_meeting[p] == meeting_idx)
    s.add(Distinct([pos_to_meeting[p] for p in range(n)]))
    
    # Travel time constraints between consecutive meetings
    for p in range(n-1):
        i = pos_to_meeting[p]
        j = pos_to_meeting[p+1]
        travel_time = travel_matrix[i][j]
        s.add(start[i] + durations[i] + travel_time <= start[j])
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Extract meeting order from positions
        meeting_order = []
        for p in range(n):
            idx = model.evaluate(pos_to_meeting[p]).as_long()
            meeting_order.append(idx)
        
        # Create itinerary in chronological order
        for idx in meeting_order:
            s_time = model.evaluate(start[idx]).as_long()
            e_time = s_time + durations[idx]
            
            # Convert to time string
            hour = 10 + s_time // 60
            minute = s_time % 60
            start_time = f"{hour}:{minute:02d}"
            
            hour = 10 + e_time // 60
            minute = e_time % 60
            end_time = f"{hour}:{minute:02d}"
            
            itinerary.append({
                'action': 'meet',
                'person': names[idx],
                'start_time': start_time,
                'end_time': end_time
            })
        
        print(f"Plan found: {{'itinerary': {itinerary}}}")
    else:
        print("No valid plan found.")

if __name__ == "__main__":
    main()