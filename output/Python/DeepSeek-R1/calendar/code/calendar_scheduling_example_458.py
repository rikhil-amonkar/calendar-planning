def find_meeting_time():
    work_hours = (9, 17)  # 9:00 to 17:00
    participants = {
        'Wayne': [],
        'Melissa': [(10, 11), (12.5, 14), (15, 15.5)],
        'Catherine': [],
        'Gregory': [(12.5, 13), (15.5, 16)],
        'Victoria': [(9, 9.5), (10.5, 11.5), (13, 14), (14.5, 15), (15.5, 16.5)],
        'Thomas': [(10, 12), (12.5, 13), (14.5, 16)],
        'Jennifer': [(9, 9.5), (10, 10.5), (11, 13), (13.5, 14.5), (15, 15.5), (16, 16.5)]
    }
    
    # Wayne's preference: not before 14:00
    possible_start = 14.0  # 14:00 in decimal
    
    # Convert time to decimal for easier comparison
    for start in [14.0, 14.5, 15.0, 15.5, 16.0, 16.5]:
        end = start + 0.5  # 30 minutes duration
        if end > 17.0:
            continue
        
        # Check all participants
        conflict = False
        for person, meetings in participants.items():
            # Check Wayne's preference
            if person == 'Wayne' and start < 14.0:
                conflict = True
                break
            
            # Check existing meetings
            for (meeting_start, meeting_end) in meetings:
                if not (end <= meeting_start or start >= meeting_end):
                    conflict = True
                    break
            if conflict:
                break
        
        if not conflict:
            # Convert decimal back to time string
            def decimal_to_time(decimal):
                hours = int(decimal)
                minutes = int((decimal - hours) * 60)
                return f"{hours:02d}:{minutes:02d}"
            
            start_str = decimal_to_time(start)
            end_str = decimal_to_time(end)
            return f"Monday {start_str}-{end_str}"
    
    return "No time found"

meeting_time = find_meeting_time()
print(meeting_time)