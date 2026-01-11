# Define work hours and busy periods
work_hours = range(900, 1700)
megan_busy = {
    'Monday': [(1300, 1330), (1400, 1530)],
    'Tuesday': [(900, 930), (1200, 1230), (1600, 1700)],
    'Wednesday': [(930, 1000), (1030, 1130), (1230, 1400), (1600, 1630)],
    'Thursday': [(1330, 1430), (1500, 1530)]
}

daniel_busy = {
    'Monday': [(1000, 1130), (1230, 1500)],
    'Tuesday': [(900, 1000), (1030, 1700)],
    'Wednesday': [(900, 1000), (1030, 1130), (1200, 1700)],
    'Thursday': [(900, 1200), (1230, 1430), (1500, 1530), (1600, 1700)]
}

def find_free_periods(busy_periods):
    # Start with full work hours
    free_periods = [(900, 1700)]
    
    for start, end in busy_periods:
        new_free_periods = []
        for f_start, f_end in free_periods:
            if end <= f_start or start >= f_end:
                # No overlap, keep the period as is
                new_free_periods.append((f_start, f_end))
            else:
                # Overlap found, split the free period
                if start > f_start:
                    new_free_periods.append((f_start, start))
                if end < f_end:
                    new_free_periods.append((end, f_end))
        free_periods = new_free_periods
    
    return free_periods

def find_meeting_time(megan_busy, daniel_busy):
    for day in ['Monday', 'Tuesday', 'Wednesday', 'Thursday']:
        megan_free = find_free_periods(megan_busy[day])
        daniel_free = find_free_periods(daniel_busy[day])
        
        # Find common free periods
        common_free = []
        i, j = 0, 0
        while i < len(megan_free) and j < len(daniel_free):
            m_start, m_end = megan_free[i]
            d_start, d_end = daniel_free[j]
            
            # Find overlap
            overlap_start = max(m_start, d_start)
            overlap_end = min(m_end, d_end)
            
            if overlap_start < overlap_end:
                common_free.append((overlap_start, overlap_end))
            
            # Move to the next period
            if m_end < d_end:
                i += 1
            else:
                j += 1
        
        # Check for a 1-hour slot in common free periods
        for start, end in common_free:
            if end - start >= 100:
                return f"{start // 100}:{start % 100:02}:{(start + 100) // 100}:{(start + 100) % 100:02}", day
    
    return None, None

meeting_time, meeting_day = find_meeting_time(megan_busy, daniel_busy)
print(f"Meeting time: {meeting_time} on {meeting_day}")