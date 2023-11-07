# Module: MutableCollections

class HashMap:
  def __init__(self):
    self.data = dict([])

  def Put(self, k, v):
    self.data[k] = v

  def HasKey(self, k):
    self.data.has_key(k)
    
  def Select(self, k):
    return self.data[k]

  def Remove(self, k):
    del self.data[k]

  def Size(self):
    len(self.data)