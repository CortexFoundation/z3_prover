#ifndef Z3_PROVER_REGISTRY_H
#define Z3_PROVER_REGISTRY_H

#include <map>
#include <string>
#include <vector>
#include <exception>

#include "base.h"

namespace z3 {
namespace utils {

template<typename EntryType>
class Registry {
 public:
  inline static const std::vector<const EntryType*>& List() {
    return Get()->const_list_;
  }

  inline static std::vector<std::string> ListAllNames() {
    const std::map<std::string, EntryType*> &fmap = Get()->fmap_;
    typename std::map<std::string, EntryType*>::const_iterator p;
    std::vector<std::string> names;
    for (p = fmap.begin(); p != fmap.end(); ++p) {
      names.push_back(p->first);
    }
    return names;
  }

  inline static const EntryType* Find(const std::string &name) {
    const std::map<std::string, EntryType*> &fmap = Get()->fmap_;
    typename std::map<std::string, EntryType*>::const_iterator
      p = fmap.find(name);
    if (p != fmap.end()) {
      return p->second;
    } else {
      return nullptr;
    }
  }

  inline void AddAlias(const std::string& key_name,
                       const std::string& alias) {
    EntryType* e = fmap_.at(key_name);
    if (fmap_.count(alias)) {
      CHECK_EQ(e, fmap_.at(alias))
          << "Trying to register alias " << alias << " for key " << key_name
          << " but " << alias << " is already taken";
    } else {
      fmap_[alias] = e;
    }
  }

  inline EntryType& __REGISTER__(const std::string &name) {
    if (fmap_.count(name) > 0U) {
      throw std::runtime_error("Entry " + name + " already registered.");
    }
    EntryType *e = new EntryType();
    e->name = name;
    fmap_[name] = e;
    const_list_.push_back(e);
    entry_list_.push_back(e);
    return *e;
  }

  inline EntryType& __REGISTER_OR_GET__(const std::string& name) {
    if (fmap_.count(name) == 0) {
      return __REGISTER__(name);
    } else {
      return *fmap_.at(name);
    }
  }

  static Registry* Get();

 private:
  std::vector<EntryType*> entry_list_;
  std::vector<const EntryType*> const_list_;
  std::map<std::string, EntryType*> fmap_;
  Registry() {}
  ~Registry() {
    for (size_t i = 0; i < entry_list_.size(); ++i) {
      delete entry_list_[i];
    }
  }
};

#define Z3UTIL_REGISTRY_ENABLE(EntryType)                                 \
  template<>                                                            \
  Registry<EntryType > *Registry<EntryType >::Get() {                   \
    static Registry<EntryType > inst;                                   \
    return &inst;                                                       \
  }                                                                     \

#define Z3UTIL_REGISTRY_REGISTER(EntryType, EntryTypeName, Name)          \
  static Z3UTIL_ATTRIBUTE_UNUSED EntryType & __make_ ## EntryTypeName \
  ## _ ## Name ## __ = \
      ::utils::Registry<EntryType>::Get()->__REGISTER__(#Name)           \

}
}

#endif // Z3_PROVER_REGISTRY_H
