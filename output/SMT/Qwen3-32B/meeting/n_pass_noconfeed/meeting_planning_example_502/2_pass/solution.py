if is_included[i].as_string() in model:
    if model.eval(is_included[i]):
        included.append(i)