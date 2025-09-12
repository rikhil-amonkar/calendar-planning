for i in range(len(meet)):
    m = model.eval(meet[i])
    m_val = m.as_long()
    if m_val != -1:
        # Process m_val
        pass